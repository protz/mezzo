(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)

type index =
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

    (* We adopt a locally nameless style. Local names are [TyVar]s, global
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

  (* A mark that is used during various traversals of the [state]. *)
  mark: Mark.t;
}

and binding =
  binding_head * raw_binding

and binding_head = {
  names: Variable.name list;
  binding_mark: Mark.t;
}

and raw_binding =
  TypeBinding of type_binder | ExprBinding of expr_binder

and type_binder = {
  (* Definition: abstract, concrete, or flexible *)
  definition: type_def;
  (* Associated fact. *)
  fact: fact;
}

and expr_binder = {
  permissions: typ list;
}

(* The empty environment. *)
let empty_env = {
  type_for_datacon = DataconMap.empty;
  state = PersistentUnionFind.init ();
  mark = Mark.create ();
}

(* Dealing with the union-find nature of the environment. *)
let same env p1 p2 =
  PersistentUnionFind.same p1 p2 env.state
;;

(* Merge while keeping the descriptor of the leftmost argument. *)
let merge_left env p2 p1 =
  { env with state = PersistentUnionFind.union p1 p2 env.state }
;;

(* ---------------------------------------------------------------------------- *)

(* Fun with de Bruijn indices. *)

(* [equal env t1 t2] provides an equality relation between [t1] and [t2] modulo
 * equivalence in the [PersistentUnionFind]. *)
let equal env (t1: typ) (t2: typ) =
  let rec equal (t1: typ) (t2: typ) =
    match t1, t2 with
      (* Special type constants. *)
    | TyUnknown, TyUnknown
    | TyDynamic, TyDynamic ->
        true

    | TyVar i, TyVar i' ->
        i = i'

    | TyPoint p1, TyPoint p2 ->
        same env p1 p2

    | TyExists ((_, k1), t1), TyExists ((_, k2), t2)
    | TyForall ((_, k1), t1), TyForall ((_, k2), t2) ->
        k1 = k2 && equal t1 t2

    | TyArrow (t1, t'1), TyArrow (t2, t'2)
    | TyApp (t1, t'1), TyApp (t2, t'2)  ->
        equal t1 t2 && equal t'1 t'2

    | TyTuple ts1, TyTuple ts2 ->
        List.fold_left2 (fun acc t1 t2 ->
          match t1, t2 with
          | TyTupleComponentValue t1, TyTupleComponentValue t2
          | TyTupleComponentPermission t1, TyTupleComponentPermission t2 ->
              acc && equal t1 t2
          | _ ->
              false) true ts1 ts2

    | TyConcreteUnfolded (name1, fields1), TyConcreteUnfolded (name2, fields2) ->
        Datacon.equal name1 name2 &&
        List.fold_left2 (fun acc f1 f2 ->
          match f1, f2 with
          | FieldValue (f1, t1), FieldValue (f2, t2) ->
              acc && Field.equal f1 f2 && equal t1 t2
          | FieldPermission t1, FieldPermission t2 ->
              acc && equal t1 t2
          | _ ->
              false) true fields1 fields2

    | TySingleton t1, TySingleton t2 ->
        equal t1 t2


    | TyStar (p1, q1), TyStar (p2, q2)
    | TyAnchoredPermission (p1, q1), TyAnchoredPermission (p2, q2) ->
        equal p1 p2 && equal q1 q2

    | TyEmpty, TyEmpty ->
        true

    | _ ->
        false
  in
  equal t1 t2
;;

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

(* Substitute [t2] for [i] in [t1]. This function is easy because [t2] is
 * expected not to have any free [TyVar]s: they've all been converted to
 * [TyPoint]s. Therefore, [t2] will *not* be lifted when substituted for [i] in
 * [t1]. *)
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

let instantiate_branch branch args =
  let args = List.rev args in
  let branch = Hml_List.fold_lefti (fun i branch arg ->
    subst_data_type_def_branch arg i branch) branch args
  in
  branch
;;


(* ---------------------------------------------------------------------------- *)

(* Various functions related to binding and finding. *)

let head name =
  {
    names = [name];
    binding_mark = Mark.create ();
  }
;;

let bind_expr (env: env) (name: Variable.name):
    env * point =
  let binding = head name, ExprBinding { permissions = []; } in
  let point, state = PersistentUnionFind.create binding env.state in
  { env with state }, point
;;

let bind_type (env: env) (name: Variable.name) (fact: fact) (definition: type_def):
    env * point =
  let binding = head name, TypeBinding { fact; definition } in
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

let bind_param_at_index_in_data_type_def_branches
    (env: env)
    (name: Variable.name)
    (fact: fact)
    (definition: type_def)
    (index: index)
    (branches: data_type_def_branch list): env * data_type_def_branch list =
  (* This needs a special treatment because the type parameters are not binders
   * per se (unlike TyForall, for instance...). *)
  let env, point = bind_type env name fact definition in
  let branches =
    List.map (subst_data_type_def_branch (TyPoint point) index) branches
  in
  env, branches
;;

let find_type (env: env) (point: point): Variable.name * type_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, TypeBinding binding ->
      List.hd names, binding
  | _, ExprBinding _ ->
      Log.error "Binder is not a type"
;;

let find_expr (env: env) (point: point): Variable.name * expr_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, ExprBinding binding ->
      List.hd names, binding
  | _, TypeBinding _ ->
      Log.error "Binder is not an expr"
;;

let name_for_binder (env: env) (point: point): string option =
  match PersistentUnionFind.find point env.state with
  | { names = name :: _; _ }, _ ->
      Some (Variable.print name)
  | _ ->
      None
;;

let name_for_expr (env: env) (point: point): string option =
  match PersistentUnionFind.find point env.state with
  | { names = name :: _; _ }, ExprBinding _ ->
      Some (Variable.print name)
  | { names = []; _ }, ExprBinding _ ->
      None 
  | _, TypeBinding _ ->
      Log.error "Binder is not an expr"
;;

let name_for_type (env: env) (point: point): string option =
  match PersistentUnionFind.find point env.state with
  | { names = name :: _; _ }, TypeBinding _ ->
      Some (Variable.print name)
  | { names = []; _ }, TypeBinding _ ->
      None 
  | _, ExprBinding _ ->
      Log.error "Binder is not a type"
;;

(* Functions for traversing the binders list. Bindings are traversed in an
 * unspecified, but fixed, order. The [replace_*] functions preserve the order.
 *
 * Indeed, it turns out that the implementation of [PersistentUnionFind] is such
 * that:
 * - when updating a descriptor, the entry in the persistent store is
 * udpated in the same location,
 * - [map_types] is implemented using [PersistentUnionFind.fold] which is in
 * turn implemented using [PersistentRef.fold], itself a proxy for
 * [Patricia.Little.fold]. The comment in [patricia.ml] tells us that fold
 * runs over the keys in an unspecified, but fixed, order.
*)

let map_types env f =
  Hml_List.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | ({ names; _ }, TypeBinding b) -> Some (f names b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map_exprs env f =
  Hml_List.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | ({ names; _ }, ExprBinding b) -> Some (f names b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map env f =
  List.rev
    (PersistentUnionFind.fold
      (fun acc _k ({ names; _ }, binding) -> f names binding :: acc)
      [] env.state)
;;

let fold env f acc =
  PersistentUnionFind.fold (fun acc k _v ->
    f acc k)
  acc env.state
;;

let fold_types env f acc =
  PersistentUnionFind.fold (fun acc k ({ names; _ }, binding) ->
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

(* Dealing with marks. *)

let get_mark (env: env) (point: point): Mark.t =
  let { binding_mark; _ }, _ = PersistentUnionFind.find point env.state in
  binding_mark
;;

let set_mark (env: env) (point: point) (binding_mark: Mark.t): env =
  { env with state =
      PersistentUnionFind.update (fun (head, binding) ->
        { head with binding_mark }, binding
      ) point env.state
  }
;;

let refresh_mark (env: env): env =
  { env with mark = Mark.create () }
;;

(* The utility functions below should save us the hassle of matching. *)

let permissions_for_ident (env: env) (point: point): expr_binder =
  snd (find_expr env point)
;;

let fact_for_type (env: env) (point: point): fact =
  let _, { fact; _ } = find_type env point in
  fact
;;

let branches_for_type (env: env) (point: point): data_type_def_branch list option =
  match find_type env point with
  | _, { definition = Concrete def; _ } ->
      let _, _name, _kind, branches = def in
      Some branches
  | _ ->
      None
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

let def_for_type (env: env) (point: point): type_def =
  (snd (find_type env point)).definition
;;

let def_for_datacon (env: env) (datacon: Datacon.name): data_type_def =
  match DataconMap.find_opt datacon env.type_for_datacon with
  | Some point ->
      begin match def_for_type env point with
      | Concrete def ->
          def
      | _ ->
          assert false
      end
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let is_abstract (env: env) (point: point): bool =
  match def_for_type env point with
  | Abstract _ ->
      true
  | _ -> false
;;

let is_concrete (env: env) (point: point): bool =
  match def_for_type env point with
  | Concrete _ ->
      true
  | _ -> false
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
        string (Option.extract (name_for_binder env point))

    | TyVar _ ->
        Log.error "All variables should've been bound at this stage"

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
        lbracket ^^
        join
          empty
          ((List.map (fun b -> if b then string "x" else string "-")) (Array.to_list bitmap)) ^^
        rbracket
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
    let print_permissions { permissions }: document =
      let permissions = List.map (print_type env) permissions in
      (*let exclusive = List.map
        (fun doc -> colors.underline ^^ doc ^^ colors.default) exclusive
      in*)
      join (comma ^^ space) permissions
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

  let ptype (env, t) =
    print_type env t
  ;;

  let print_binders (env: env): document =
    print_string "Γ (unordered) = " ^^
    join
      (semi ^^ space)
      (map env (fun names _ -> join (string " = ") (List.map print_var names)))
  ;;


end
