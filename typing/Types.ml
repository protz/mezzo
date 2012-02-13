(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)

type index =
  int

type level =
  int

type kind =
  SurfaceSyntax.kind

let flatten_kind =
  SurfaceSyntax.flatten_kind

module IndexMap = Hml_Map.Make(struct
  type t = index
  let compare = Pervasives.compare
end)

module LevelMap = IndexMap

type type_binding =
    SurfaceSyntax.type_binding

module DataconMap = Hml_Map.Make(struct
  type t = Datacon.name
  let compare = Pervasives.compare
end)

(* Record fields remain named. *)

module Field = Variable

(* The annotations [Consumes] and [ConsumesAndProduces] that appear in the
   surface syntax are desugared. They do not appear at this level. *)

(* In the surface syntax, tuple types can bind names for their components.
   Here, this is desugared using singleton types, universal quantification,
   and existential quantification. Tuple type components are now anonymous. *)

(* TEMPORARY we need a notion of type equality, or subtyping, that deals with
   quantifiers in a transparent way -- especially the quantifiers introduced
   by the translation of named tuple components down to this kernel syntax.
   E.g. we need (the translation of) [t] to be interconvertible with (the
   translation of) [(x: t)], which is [exists x :: term. (=x, permission x: t)].
   Hmm, tricky, tricky. Do we really want to go this way? *)

(* TEMPORARY also, subtyping must take into account the AC axioms for TyStar,
   the fact that TyEmpty is neutral for TyStar, and (perhaps) the fact that
   duplicable permissions are idempotent for TyStar. Tricky, tricky. *)

(* TEMPORARY also, subtyping must take into account the fact that tuple
   components which are anonymous permissions can freely move around
   within a tuple. Hmm, hmm. *)

(* TEMPORARY perhaps we could completely avoid the need for subtyping
   (and solve all three problems above) by working with explicit
   eta-expansions instead. This requires thought! *)

type typ =
    (* Special type constants. *)
  | TyUnknown
  | TyDynamic

    (* Flexible type variables. *)
  | TyFlexible of PersistentUnionFind.point

    (* Type variables and quantification. Type application. *)
  | TyVar of index
  | TyForall of type_binding * typ
  | TyExists of type_binding * typ
  | TyApp of typ * typ

    (* Structural types. *)
  | TyTuple of tuple_type_component list
  | TyConcreteUnfolded of data_type_def_branch

    (* Singleton types. *)
  | TySingleton of typ

    (* Function types. *)
  | TyArrow of typ * typ

    (* Permissions. *)
  | TyAnchoredPermission of typ * typ
  | TyEmpty
  | TyStar of typ * typ
  (* TEMPORARY perhaps TyEmpty and TyStar can be removed because we already
               have TyTuple, which could serve to construct tuples of
               permissions. Investigate. *)

and tuple_type_component =
  | TyTupleComponentValue of typ
  | TyTupleComponentPermission of typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of (Field.name * typ)
  | FieldPermission of typ

and data_type_def =
  SurfaceSyntax.data_type_flag * Variable.name * kind * data_type_def_branch list

and abstract_type_def =
  Variable.name * kind

and type_def =
  | Concrete of data_type_def
  | Abstract of abstract_type_def

(* ---------------------------------------------------------------------------- *)

(* Program-wide environment. *)

(** We abstract away all the operations on our data structure (currenlty, lists)
 * so that it's easy to switch to a more efficient data structure afterwards. *)
module ByIndex: sig
  type 'a t
  (* Total number of bindings in an environment. *)
  val cardinal: 'a t -> int
  (* Add a new binding in the environment. *)
  val add: 'a -> 'a t -> 'a t
  (* This returns an option so that one can do deep pattern-matching easily. *)
  val find_opt: int -> 'a t -> 'a option
  (* Use when the binding ought to be found. *)
  val find: int -> 'a t -> 'a
  (* Return a subset of the environment with only the topmost [n] bindings. *)
  val toplevel: int -> 'a t -> 'a t
  (* The empty environment. *)
  val empty: 'a t
  (* Map from the topmost binding down to the innermost. *)
  val map_down: ('a -> 'b) -> 'a t -> 'b list
  (* Iter from the topmost binding down to the innermost. *)
  val iter_upi: (int -> 'a -> unit) -> 'a t -> unit
  (* Fold *)
  val fold: (int -> 'acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
  (* Replace the entry at index. *)
  val replace: int -> ('a -> 'a) -> 'a t -> 'a t
end = struct
  type 'a t = 'a list
  let cardinal =
    List.length
  ;;
  let add x l =
    x :: l
  ;;
  let find_opt i l =
    Hml_List.nth_opt l i
  ;;
  let find i l =
    List.nth l i
  ;;
  let empty =
    []
  ;;
  let toplevel i l =
    let l = List.rev l in
    let rec chop remaining acc = function
    | _ when remaining = 0 ->
        acc
    | hd :: tl ->
        chop (remaining - 1) (hd :: acc) tl
    | [] ->
        raise Not_found
    in
    chop i [] l
  ;;
  let map_down =
    List.rev_map
  ;;
  let iter_upi =
    List.iteri
  ;;
  let fold =
    Hml_List.fold_lefti
  ;;
  let replace j f the_list =
    List.mapi (fun i elt -> if j = i then f elt else elt) the_list
  ;;
end

(* A fact refers to any type variable available in scope; the first few facts
 * refer to toplevel data types, and the following facts refer to type variables
 * introduced in the scope, because, for instance, we went through a binder in a
 * function type.
 *
 * The [Fuzzy] case is used when we are inferring facts for a top-level data
 * type; we need to introduce the data type's parameters in the environment, but
 * the correponding facts are evolving as we work through our analysis. *)
type fact = Exclusive | Duplicable of bitmap | Affine | Fuzzy

(* The 0-th element is the first parameter of the type, and the value is true if
  * it has to be duplicable for the type to be duplicable. *)
and bitmap = bool array

(** This is the environment that we use throughout HaMLeT. Our representation
 * uses De Bruijn indexes. Right now, they're implemented using lists, but we
 * may switch to a more efficient data structure later on if needed. *)
type env = {
  (* For any [datacon], get the index of the corresponding type. *)
  type_for_datacon: index DataconMap.t;

  (* The map above gives indices that are valid in the top-level context. That
   * is to say, if Γ = α, bar, foo where only bar and foo are top-level data
   * types, with foo being defined first, foo's index in the current scope is 2,
   * but [type_for_datacon] will map foo to 1, because [type_for_datacon]
   * assumes only the top-level context, that is Γ = bar, foo. Therefore, we
   * need to keep the number of types defined in the top-level context. This
   * number may change if, for instance, we go through another data type
   * definition group. *)
  toplevel_size: int;

  (** The persistent version the union-find algorithm associates points with
   * permissions. *)
  state: permissions PersistentUnionFind.state;

  (** The state of flexible variables. We introduce flexible variables to
   * perform some sort of limited, local type inference. Flexible variables can
   * be unified together, and unified with a “real” type.
   *)
  flexible_state: descriptor PersistentUnionFind.state;

  (* Everything about the type binders in scope. *)
  type_bindings: type_entry ByIndex.t;

  (* Everything about the expr binders in scope. *)
  expr_bindings: expr_entry ByIndex.t;
}

(* This is an entry in our [ByIndex.t] for binders in types. *)
and type_entry = {
  (* Name, for debugging. Known at bind-time. *)
  tname: Variable.name;
  (* Definition: abstract, or concrete. *)
  definition: type_def;
  (* Associated fact. *)
  fact: fact;
}

(* This is an entry in our [ByIndex.t] for binders in expressions. *)
and expr_entry = {
  (* Name, for debugging. Known at bind-time. *)
  ename: Variable.name;

  (** We map a program identifier to the corresponding persistent union-find
   * point.  This implictly represents the fact that we have equations between
   * program identifiers. The various maps and lists thus refer to
   * union-find points, not program identifiers. *)
  point: PersistentUnionFind.point;
}

(** We separate duplicable permissions and exclusive permissions *)
and permissions = {
  duplicable: typ list;
  exclusive: typ list;
}

and descriptor = {
  structure: typ option; (* No mutable keyword here, since we're using a functional union-find. *)
}

(* The empty environment. *)
let empty_env = {
  type_for_datacon = DataconMap.empty;
  toplevel_size = 0;
  state = PersistentUnionFind.init ();
  flexible_state = PersistentUnionFind.init ();
  type_bindings = ByIndex.empty;
  expr_bindings = ByIndex.empty;
}

(* ---------------------------------------------------------------------------- *)

(* Fun with de Bruijn indices. *)

let lift (k: int) (t: typ) =
  let rec lift (i: int) (t: typ) =
    match t with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic ->
        t

      (* Flexible type variables. *)
    | TyFlexible _ ->
        Log.error "Not implemented yet."

    | TyVar j ->
        if j < i then
          TyVar j
        else
          TyVar (j + k)

    | TyForall (binder, t) ->
        TyForall (binder, lift (i+1) t)

    | TyExists (binder, t) ->
        TyExists (binder, lift (i+1) t)

    | TyApp (t1, t2) ->
        TyApp (lift i t1, lift i t2)

    | TyTuple ts ->
        TyTuple (List.map (function
          | TyTupleComponentValue t ->
              TyTupleComponentValue (lift i t)
          | TyTupleComponentPermission t ->
              TyTupleComponentPermission (lift i t)) ts)

    | TyConcreteUnfolded (name, fields) ->
       TyConcreteUnfolded (name, List.map (function
         | FieldValue (field_name, t) -> FieldValue (field_name, lift i t)
         | FieldPermission t -> FieldPermission (lift i t)) fields)

    | TySingleton t ->
        TySingleton (lift i t)

    | TyArrow (t1, t2) ->
        TyArrow (lift i t1, lift i t2)

    | TyAnchoredPermission (p, q) ->
        TyAnchoredPermission (lift i p, lift i q)

    | TyEmpty ->
        t

    | TyStar (p, q) ->
        TyStar (lift i p, lift i q)
  in
  lift 0 t
;;

let lift1 =
  lift 1
;;

let lift_data_type_def (k: int) (def: data_type_def): data_type_def =
  let flag, name, kind, branches = def in
  let branches = List.map (fun (datacon, fields) ->
    datacon, List.map (function
      | FieldPermission t ->
          FieldPermission (lift k t)
      | FieldValue (field_name, t) ->
          FieldValue (field_name, lift k t)
    ) fields) branches
  in
  flag, name, kind, branches
;;

(* Substitute [t2] for [i] in [t1]. *)
let subst (t2: typ) (i: int) (t1: typ) =
  let rec subst t2 i t1 =
    match t1 with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic ->
        t1

      (* Flexible type variables. *)
    | TyFlexible _ ->
        Log.error "Not implemented yet."

    | TyVar j ->
        if j = i then
          t2
        else if j < i then
          TyVar j
        else
          TyVar (j - 1)

    | TyForall (binder, t) ->
        TyForall (binder, subst t2 (i+1) t)

    | TyExists (binder, t) ->
        TyExists (binder, subst t2 (i+1) t)

    | TyApp (t, t') ->
        TyApp (subst t2 i t, subst t2 i t')

    | TyTuple ts ->
        TyTuple (List.map (function
          | TyTupleComponentValue t ->
              TyTupleComponentValue (subst t2 i t)
          | TyTupleComponentPermission t ->
              TyTupleComponentPermission (subst t2 i t)) ts)

    | TyConcreteUnfolded (name, fields) ->
       TyConcreteUnfolded (name, List.map (function
         | FieldValue (field_name, t) -> FieldValue (field_name, subst t2 i t)
         | FieldPermission t -> FieldPermission (subst t2 i t)) fields)

    | TySingleton t ->
        TySingleton (subst t2 i t)

    | TyArrow (t, t') ->
        TyArrow (subst t2 i t, subst t2 i t')

    | TyAnchoredPermission (p, q) ->
        TyAnchoredPermission (subst t2 i p, subst t2 i q)

    | TyEmpty ->
        t1

    | TyStar (p, q) ->
        TyStar (subst t2 i p, subst t2 i q)
  in
  subst t2 i t1
;;

(* ---------------------------------------------------------------------------- *)

(* Various helper functions. *)

let bind_expr (env: env) (ename: Variable.name): env =
  (* TODO: add the corresponding singleton type variable in the environment. *)
  let permissions = { duplicable = []; exclusive = [] } in
  let point, state = PersistentUnionFind.create permissions env.state in 
  let entry = { ename; point } in
  { env with expr_bindings = ByIndex.add entry env.expr_bindings; state }
;;

let bind_type (env: env) (tname: Variable.name) (fact: fact) (definition: type_def): env =
  let entry = { tname; fact; definition } in
  { env with type_bindings = ByIndex.add entry env.type_bindings }
;;

let name_for_expr (env: env) (index: index): string =
  match ByIndex.find_opt index env.expr_bindings with
  | Some { ename; _ } ->
      Variable.print ename
  | None ->
      Log.error "There is no expr binder at index %d" index
;;

let name_for_type (env: env) (index: index): string =
  match ByIndex.find_opt index env.type_bindings with
  | Some { tname; _ } ->
      Variable.print tname
  | None ->
      Log.error "There is no type binder at index %d" index
;;


(* TEMPORARY we will want a function that allows one to change the assumption on
 * a bound type variable, for instance when crossing [(duplicable a) =>] in a
 * function type. *)

let permissions_for_ident (env: env) (index: index): permissions =
  let { point; _ } = ByIndex.find index env.expr_bindings in
  PersistentUnionFind.find point env.state

let fact_for_type (env: env) (index: index): fact =
  match ByIndex.find_opt index env.type_bindings with
  | Some { fact; _ } ->
      fact
  | None ->
      Log.error "There is no type binder at index %d" index
;;

let branches_for_type (env: env) (index: index): data_type_def_branch list =
  match ByIndex.find_opt index env.type_bindings with
  | Some { definition = Concrete def; _ } ->
      let k = ByIndex.cardinal env.type_bindings - env.toplevel_size in
      let _, _name, _kind, branches = lift_data_type_def k def in
      branches
  | Some { definition = Abstract (name, _); _ } ->
      Log.error "No branches for type %a, it is abstract" Variable.p name
  | None ->
      Log.error "There is no type binder at index %d" index
;;

let kind_for_type (env: env) (index: index): kind =
  match ByIndex.find_opt index env.type_bindings with
  | Some { definition = Concrete (_, _name, kind, _) | Abstract (_name, kind); _ } ->
      kind
  | None ->
      Log.error "There is no type binders at index %d" index
;;

let def_for_datacon (env: env) (datacon: Datacon.name): data_type_def =
  match DataconMap.find_opt datacon env.type_for_datacon with
  | Some index ->
      let k = ByIndex.cardinal env.type_bindings - env.toplevel_size in
      begin match ByIndex.find (index + k) env.type_bindings with
      | { definition = Concrete def; _ } ->
          lift_data_type_def k def
      | { definition = Abstract _; _ } ->
          assert false
      end
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let arity_for_data_type (env: env) (index: index): int =
  let _, tl = flatten_kind (kind_for_type env index) in
  List.length tl
;;

(* TODO: we should flatten type applications as soon as we can... *)
let flatten_tyapp t =
  let rec flatten_tyapp acc = function
    | TyApp (t1, t2) ->
        flatten_tyapp (t2 :: acc) t1
    | _ as x ->
        x, acc
  in
  flatten_tyapp [] t
;;

let bind_datacon_parameters (env: env) (kind: kind): env =
  let _return_kind, params = flatten_kind kind in
  (* Turn the list of parameters into letters *)
  let letters: string list = Hml_Pprint.name_gen (List.length params) in
  let env = List.fold_left2 (fun env letter kind ->
    let letter = Variable.register letter in
    bind_type env letter Fuzzy (Abstract (letter, kind))
  ) env letters params in
  env
;;


(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  open Hml_Pprint

  (* --------------------------------------------------------------------------- *)

  let print_var var =
    print_string (Variable.print var)
  ;;

  let print_datacon datacon =
    print_string (Datacon.print datacon)
  ;;

  let print_field field =
    print_string (Field.print field)
  ;;

  let rec print_kind =
    let open SurfaceSyntax in
    function
    | KTerm ->
        string "term"
    | KPerm ->
        string "perm"
    | KType ->
        string "∗"
    | KArrow (k1, k2) ->
        print_kind k1 ^^ space ^^ arrow ^^ space ^^ print_kind k2
  ;;

  (* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
  let p_kind buf kind =
    Pprint.PpBuffer.pretty 1.0 80 buf (print_kind kind)
  ;;

  let rec print_quantified
      (env: env)
      (q: string)
      (name: Variable.name) 
      (kind: SurfaceSyntax.kind)
      (typ: typ) =
    print_string q ^^ lparen ^^ print_var name ^^ space ^^ ccolon ^^ space ^^
    print_kind kind ^^ rparen ^^ dot ^^ jump (print_type env typ)

  (* TEMPORARY this does not respect precedence and won't insert parentheses at
   * all! *)
  and print_type env = function
    | TyUnknown ->
        string "unknown"

    | TyDynamic ->
        string "dynamic"

    | TyVar index ->
        string (name_for_type env index)

    | TyFlexible _ ->
        string "[flexible]"

    | TyForall ((name, kind), typ) ->
        let env = bind_type env name Affine (Abstract (name, kind)) in
        print_quantified env "∀" name kind typ

    | TyExists ((name, kind), typ) ->
        let env = bind_type env name Affine (Abstract (name, kind)) in
        print_quantified env "∃" name kind typ

    | TyApp (t1, t2) ->
        print_type env t1 ^^ space ^^ print_type env t2

    | TyTuple components ->
        lparen ^^
        join
          (comma ^^ space)
          (List.map (print_tuple_type_component env) components) ^^
        rparen

    | TyConcreteUnfolded branch ->
        print_data_type_def_branch env branch

      (* Singleton types. *)
    | TySingleton typ ->
        equals ^^ print_type env typ

      (* Function types. *)
    | TyArrow (t1, t2) ->
        print_type env t1 ^^ space ^^ arrow ^^
        group (break1 ^^ print_type env t2)

      (* Permissions. *)
    | TyAnchoredPermission (t1, t2) ->
        print_type env t1 ^^ colon ^^ space ^^ print_type env t2

    | TyEmpty ->
        string "empty"

    | TyStar (t1, t2) ->
        print_type env t1 ^^ star ^^ print_type env t2

  and print_tuple_type_component env = function
    | TyTupleComponentValue typ ->
        print_type env typ

    | TyTupleComponentPermission typ ->
        string "permission" ^^ space ^^ print_type env typ

  and print_data_field_def env = function
    | FieldValue (name, typ) ->
        print_field name ^^ colon ^^ jump (print_type env typ)

    | FieldPermission typ ->
        string "permission" ^^ space ^^ print_type env typ

  and print_data_type_def_branch env (branch: data_type_def_branch) =
    let name, fields = branch in
    let record =
      if List.length fields > 0 then
        space ^^ lbrace ^^
        nest 4
          (break1 ^^ join
            (semi ^^ break1)
            (List.map (print_data_field_def env) fields)) ^^
        nest 2 (break1 ^^ rbrace)
      else
        empty
    in
    print_datacon name ^^ record
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let do_print_fact (fact: fact): document =
    match fact with
    | Duplicable bitmap ->
        join
          empty
          ((List.map (fun b -> if b then string "x" else string "-")) (Array.to_list bitmap))
    | Exclusive ->
        string "exclusive"
    | Affine ->
        string "affine"
    | Fuzzy ->
        string "fuzzy"
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let print_fact (env, index: env * index): document =
    do_print_fact (fact_for_type env index);
  ;;

  let print_facts (env: env): document =
    let is name is_abstract ?params w =
      let params =
        match params with
        | Some params -> join_left space (List.map print_string params)
        | None -> empty
      in
      colors.underline ^^ print_var name ^^ params ^^
      colors.default ^^ string " is " ^^
      (if is_abstract then string "abstract and " else empty) ^^
      print_string w
    in
    let print_fact name is_abstract arity fact =
      let params = Hml_Pprint.name_gen arity in
      let is w = is name is_abstract ~params w in
      match fact with
      | Fuzzy ->
          is "fuzzy"
      | Exclusive ->
          is "exclusive"
      | Affine ->
          is "affine"
      | Duplicable bitmap ->
          let dup_params = List.map2
            (fun b param -> if b then Some param else None)
            (Array.to_list bitmap)
            params
          in
          let dup_params = Hml_List.filter_some dup_params in
          if List.length dup_params > 0 then begin
            let verb = string (if List.length dup_params > 1 then " are " else " is ") in
            let dup_params = List.map print_string dup_params in
            is "duplicable if " ^^ english_join dup_params ^^ verb ^^
            string "duplicable"
          end else begin
            is "duplicable"
          end
    in
    let lines =
      ByIndex.map_down (fun { definition; fact; } ->
        match definition with
        | Concrete (_flag, name, kind, _branches) ->
            let _hd, tl = flatten_kind kind in 
            let arity = List.length tl in
            print_fact name false arity fact
        | Abstract (name, kind) ->
            let _hd, tl = flatten_kind kind in 
            let arity = List.length tl in
            print_fact name true arity fact
      ) env.type_bindings
    in
    join hardline lines
  ;;

  let print_permissions (env: env): document =
    let print_permissions permissions: document =
      let { duplicable; exclusive } = permissions in
      let duplicable = List.map (print_type env) duplicable in
      let exclusive = List.map (print_type env) exclusive in
      let exclusive = List.map
        (fun doc -> colors.underline ^^ doc ^^ colors.default) exclusive
      in
      join (comma ^^ break1) (duplicable @ exclusive)
    in
    let header =
      let str = "PERMISSIONS:" in
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let lines = ByIndex.map_down (fun { ename; point } ->
      let permissions = PersistentUnionFind.find point env.state in
      let perms = print_permissions permissions in
      (print_var ename) ^^ colon ^^ space ^^ (nest 2 perms)
    ) env.expr_bindings in
    let lines = join break1 lines in
    header ^^ (nest 2 (break1 ^^ lines))
  ;;

  (* Example: Log.debug "%a" pdoc (f, args) *)
  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    PpBuffer.pretty 1.0 Bash.twidth buf (f env)
  ;;

  let print_types_in_scope (env: env): document =
    print_string "Γ = " ^^
    join (semi ^^ space) (ByIndex.map_down (fun { tname; _ } -> print_var tname) env.type_bindings)
  ;;


end
