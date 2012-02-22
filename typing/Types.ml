(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)

type index =
  int

type level =
  int

type point =
  PersistentUnionFind.point

type kind =
  SurfaceSyntax.kind

let flatten_kind =
  SurfaceSyntax.flatten_kind

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

    (* We adopt a locally nameless styles. Local names are [TyVar]s, global
     * names are [TyPoint]s *)
  | TyVar of index
  | TyPoint of point

    (* Quantification and type application. *)
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
  | Flexible of typ option

(* ---------------------------------------------------------------------------- *)

(* Program-wide environment. *)

(* A fact refers to any type variable available in scope; the first few facts
 * refer to toplevel data types, and the following facts refer to type variables
 * introduced in the scope, because, for instance, we went through a binder in a
 * function type.
 *
 * The [Fuzzy] case is used when we are inferring facts for a top-level data
 * type; we need to introduce the data type's parameters in the environment, but
 * the correponding facts are evolving as we work through our analysis. The
 * integer tells the number of the parameter. *)
type fact = Exclusive | Duplicable of bitmap | Affine | Fuzzy of int

(* The 0-th element is the first parameter of the type, and the value is true if
  * it has to be duplicable for the type to be duplicable. *)
and bitmap = bool array

(** This is the environment that we use throughout HaMLeT. *)
type env = {
  (* For any [datacon], get the point of the corresponding type. *)
  type_for_datacon: point DataconMap.t;

  (* This maps global names (i.e. [TyPoint]s) to their corresponding binding. *)
  state: binding PersistentUnionFind.state;
}

and binding =
  Variable.name list * raw_binding

and raw_binding =
  TypeBinding of type_binder | ExprBinding of expr_binder

and type_binder = {
  (* Definition: abstract, concrete, or flexible *)
  definition: type_def;
  (* Associated fact. *)
  fact: fact;
}

and expr_binder = {
  duplicable: typ list;
  exclusive: typ list;
}

(* The empty environment. *)
let empty_env = {
  type_for_datacon = DataconMap.empty;
  state = PersistentUnionFind.init ();
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

    | TyVar j ->
        if j < i then
          TyVar j
        else
          TyVar (j + k)

    | TyPoint _ ->
        t

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

let lift_field k = function
  | FieldValue (name, typ) ->
      FieldValue (name, lift k typ)
  | FieldPermission typ ->
      FieldPermission (lift k typ)
;;

let lift_data_type_def_branch k branch =
  let name, fields = branch in
  name, List.map (lift_field k) fields
;;

(* Substitute [t2] for [i] in [t1]. *)
let subst (t2: typ) (i: int) (t1: typ) =
  let rec subst t2 i t1 =
    match t1 with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic ->
        t1

    | TyVar j ->
        if j = i then
          t2
        else
          TyVar j

    | TyPoint _ ->
        t1

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

let subst_field t2 i = function
  | FieldValue (name, typ) ->
      FieldValue (name, subst t2 i typ)
  | FieldPermission typ ->
      FieldPermission (subst t2 i typ)
;;

let subst_data_type_def_branch t2 i branch =
  let name, fields = branch in
  name, List.map (subst_field t2 i) fields
;;


(* ---------------------------------------------------------------------------- *)

(* Various functions related to binding and finding. *)

let bind_expr (env: env) (name: Variable.name):
    env * point =
  let binding = [name], ExprBinding { duplicable = []; exclusive = [] } in
  let point, state = PersistentUnionFind.create binding env.state in
  { env with state }, point
;;

let bind_type (env: env) (name: Variable.name) (fact: fact) (definition: type_def):
    env * point =
  let binding = [name], TypeBinding { fact; definition } in
  let point, state = PersistentUnionFind.create binding env.state in
  { env with state }, point
;;

let bind_type_in_type
    (env: env)
    (name: Variable.name)
    (fact: fact)
    (definition: type_def)
    (typ: typ): env * typ =
  let env, point = bind_type env name fact definition in
  let typ = subst (TyPoint point) 0 typ in
  env, typ
;;

(* This needs a special treatment because the type parameters are not binders
 * per se (unlike TyForall, for instance...). *)
let bind_param_at_index_in_data_type_def_branches
    (env: env)
    (name: Variable.name)
    (fact: fact)
    (definition: type_def)
    (index: index)
    (branches: data_type_def_branch list): env * data_type_def_branch list =
  let env, point = bind_type env name fact definition in
  let branches =
    List.map (subst_data_type_def_branch (TyPoint point) index) branches
  in
  env, branches
;;

let find_type (env: env) (point: point): Variable.name * type_binder =
  match PersistentUnionFind.find point env.state with
  | names, TypeBinding binding ->
      List.hd names, binding
  | names, ExprBinding _ ->
      Log.error "Binder is not a type"
;;

let find_expr (env: env) (point: point): Variable.name * expr_binder =
  match PersistentUnionFind.find point env.state with
  | names, ExprBinding binding ->
      List.hd names, binding
  | name, TypeBinding _ ->
      Log.error "Binder is not an expr"
;;

let name_for_expr (env: env) (point: point): string =
  Variable.print (fst (find_expr env point))
;;

let name_for_type (env: env) (point: point): string =
  Variable.print (fst (find_type env point))
;;

(* Functions for traversing the binders list. *)

let map_types env f =
  Hml_List.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | (names, TypeBinding b) -> Some (f names b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map_exprs env f =
  Hml_List.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | (names, ExprBinding b) -> Some (f names b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map env f =
  List.rev
    (PersistentUnionFind.fold
      (fun acc _k (names, binding) -> f names binding :: acc)
      [] env.state)
;;

let fold env f acc =
  PersistentUnionFind.fold (fun acc k _v ->
    f acc k)
  acc env.state
;;

let fold_types env f acc =
  PersistentUnionFind.fold (fun acc k (names, binding) ->
    match binding with TypeBinding b -> f acc k names b | _ -> acc)
  acc env.state
;;

let replace_expr env point f =
  { env with state =
      PersistentUnionFind.update (function
        | names, ExprBinding b ->
            names, ExprBinding (f b)
        | _ ->
            Log.error "Not an expr"
      ) point env.state
  }
;;

let replace_type env point f =
  { env with state =
      PersistentUnionFind.update (function
        | names, TypeBinding b ->
            names, TypeBinding (f b)
        | _ ->
            Log.error "Not a type"
      ) point env.state
  }
;;

let permissions_for_ident (env: env) (point: point): expr_binder =
  snd (find_expr env point)
;;

let fact_for_type (env: env) (point: point): fact =
  let _, { fact; _ } = find_type env point in
  fact
;;

let branches_for_type (env: env) (point: point): data_type_def_branch list =
  match find_type env point with
  | _, { definition = Concrete def; _ } ->
      let _, _name, _kind, branches = def in
      branches
  | name, _ ->
      Log.error "No branches for type %a, it is not concrete" Variable.p name
;;

let kind_for_def (def: type_def): kind =
  match def with
  | Concrete (_, _name, kind, _) | Abstract (_name, kind) ->
      kind
  | _ ->
      Log.error "Not implemented yet"
;;

let kind_for_type (env: env) (point: point): kind =
  let _, { definition; _ } = find_type env point in
  kind_for_def definition
;;

let def_for_datacon (env: env) (datacon: Datacon.name): data_type_def =
  match DataconMap.find_opt datacon env.type_for_datacon with
  | Some point ->
      begin match snd (find_type env point) with
      | { definition = Concrete def; _ } ->
          def
      | _ ->
          assert false
      end
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let arity_for_def (def: type_def): int =
  let _, tl = flatten_kind (kind_for_def def) in
  List.length tl
;;

let arity_for_data_type (env: env) (point: point): int =
  let _, tl = flatten_kind (kind_for_type env point) in
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

let bind_datacon_parameters (env: env) (kind: kind) (branches: data_type_def_branch list):
    env * data_type_def_branch list =
  let _return_kind, params = flatten_kind kind in
  let arity = List.length params in
  (* Turn the list of parameters into letters *)
  let letters: string list = Hml_Pprint.name_gen (List.length params) in
  let env, branches = Hml_List.fold_left2i (fun i (env, branches) letter kind ->
    let letter = Variable.register letter in
    let env, branches =
      let index = arity - i - 1 in
      bind_param_at_index_in_data_type_def_branches
        env letter (Fuzzy i) (Abstract (letter, kind)) index branches
    in
    env, branches
  ) (env, branches) letters params in
  env, branches
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

    | TyPoint point ->
        string (name_for_type env point)

    | TyVar i ->
        int i
        (* Log.error "All variables should've been bound at this stage" *)

    | TyForall ((name, kind), typ) ->
        let env, typ = bind_type_in_type env name Affine (Abstract (name, kind)) typ in
        print_quantified env "∀" name kind typ

    | TyExists ((name, kind), typ) ->
        let env, typ = bind_type_in_type env name Affine (Abstract (name, kind)) typ in
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
    | Fuzzy i ->
        string "fuzzy " ^^ int i
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let print_fact (env, point: env * point): document =
    do_print_fact (fact_for_type env point);
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
      | Fuzzy _ ->
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
      map_types env (fun _ { definition; fact; } ->
        match definition with
        | Concrete (_flag, name, kind, _branches) ->
            let _hd, tl = flatten_kind kind in 
            let arity = List.length tl in
            print_fact name false arity fact
        | Abstract (name, kind) ->
            let _hd, tl = flatten_kind kind in 
            let arity = List.length tl in
            print_fact name true arity fact
        | Flexible _ ->
            Log.error "Not implemented yet"
      )
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
      join (comma ^^ space) (duplicable @ exclusive)
    in
    let header =
      let str = "PERMISSIONS:" in
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let lines = map_exprs env (fun names binder ->
      let name = List.hd names in
      let perms = print_permissions binder in
      (print_var name) ^^ colon ^^ space ^^ (nest 2 perms)
    ) in
    let lines = join break1 lines in
    header ^^ (nest 2 (break1 ^^ lines))
  ;;

  (* Example: Log.debug "%a" pdoc (f, args) *)
  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    PpBuffer.pretty 1.0 Bash.twidth buf (f env)
  ;;

  let print_binders (env: env): document =
    print_string "Γ (unordered) = " ^^
    join
      (semi ^^ space)
      (map env (fun names _ -> join (string " = ") (List.map print_var names)))
  ;;


end
