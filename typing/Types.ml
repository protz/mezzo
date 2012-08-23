(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)

type index =
  int

type point =
  PersistentUnionFind.point

type kind = SurfaceSyntax.kind = 
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

let flatten_kind =
  SurfaceSyntax.flatten_kind

(** Has this name been auto-generated or not? *)
type name = User of Variable.name | Auto of Variable.name

type location = Lexing.position * Lexing.position

type type_binding =
  name * kind * location

module DataconMap = Hml_Map.Make(struct
  type t = Datacon.name
  let compare = Pervasives.compare
end)

(* Record fields remain named. *)

module Field = Variable

type variance = Invariant | Covariant | Contravariant | Bivariant

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
  | TyTuple of typ list
  | TyConcreteUnfolded of data_type_def_branch

    (* Singleton types. *)
  | TySingleton of typ

    (* Function types. *)
  | TyArrow of typ * typ

    (* The bar *)
  | TyBar of typ * typ

    (* Permissions. *)
  | TyAnchoredPermission of typ * typ
  | TyEmpty
  | TyStar of typ * typ

    (* Constraint *)
  | TyConstraints of duplicity_constraint list * typ

and duplicity_constraint = SurfaceSyntax.data_type_flag * typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of (Field.name * typ)
  | FieldPermission of typ

type data_type_def =
  data_type_def_branch list

type type_def =
    (SurfaceSyntax.data_type_flag * data_type_def) option
  * variance list

(* ---------------------------------------------------------------------------- *)

(* Program-wide environment. *)

let (^=>) x y = x && y || not x;;

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

type structure = Rigid | Flexible of typ option

type permissions = typ list

(** This is the environment that we use throughout HaMLeT. *)
type env = {
  (* For any [datacon], get the point of the corresponding type. *)
  type_for_datacon: point DataconMap.t;

  (* This maps global names (i.e. [TyPoint]s) to their corresponding binding. *)
  state: binding PersistentUnionFind.state;

  (* A mark that is used during various traversals of the [state]. *)
  mark: Mark.t;

  (* The current location. *)
  location: location;

  (* Did we figure out that this environment is inconsistent? It may be because
   * a point acquired two exclusive permissions, or maybe because the user wrote
   * "fail" at some point. This is by no means exhaustive: we only detect a few
   * inconsistencies when we're lucky. *)
  inconsistent: bool;
}

and binding =
  binding_head * raw_binding

and binding_head = {
  (* This information is only for printing and debugging. *)
  names: name list;
  locations: location list;

  (* Is this a flexible variable, and has it been unified with something? *)
  structure: structure;

  (* The kind of this variable. If kind is TERM, then the [raw_binding] is a
   * [term_binder]. *)
  kind: kind;

  (* For some passes, we need to mark points as visited. This module provides a
   * set of functions to deal with marks. *)
  binding_mark: Mark.t;
}

and raw_binding =
  BType of type_binder | BTerm of term_binder | BPerm of perm_binder

and type_binder = {
  (* Definition: if it's a variable, there's no definition for it. If it's a
   * data type definition, we at least know the variance of its parameters. If
   * the type is concrete (e.g. [list]) there's a flag and branches, otherwise
   * it's abstract and we don't have any more information. *)
  definition: type_def option;

  (* Associated fact. *)
  fact: fact;
}

and term_binder = {
  (* A list of available permissions for that identifier. *)
  permissions: permissions;

  (* A ghost variable has been introduced, say, through [x :: TERM], and does
   * not represent something we can compile.
   *
   * TEMPORARY: as of 2012/07/12 this information is not accurate and one should
   * not rely on it. *)
  ghost: bool;
}

and perm_binder = {
  (* XXX this is temporary, we still need to think about how we should represent
   * permissions that are not attached to a particular identifier. A simple
   * strategy would be to attach to the environment a list of all points
   * representing PERM binders.
   *
   * 2012/07/12: and make sure that as soon as some flexible variable happens to
   * be unified, we run through the list of floating permissions to see if
   * [x* @ t] turned into [x @ t], which means we should attach [t] to the
   * list of available permissions for point [x]. *)
  consumed: bool;
}

(* This is not pretty, but we need some of these functions for debugging, and
 * the printer is near the end. *)

let internal_ptype = ref (fun _ -> assert false);;
let internal_pnames = ref (fun _ -> assert false);;
let internal_ppermissions = ref (fun _ -> assert false);;

(* The empty environment. *)
let empty_env = {
  type_for_datacon = DataconMap.empty;
  state = PersistentUnionFind.init ();
  mark = Mark.create ();
  location = Lexing.dummy_pos, Lexing.dummy_pos;
  inconsistent = false;
}

let locate env location =
  { env with location }
;;


(* ---------------------------------------------------------------------------- *)

(** Some functions related to the manipulation of the union-find structure of
 * the environment. *)

module PointMap = Hml_Map.Make(struct
  type t = PersistentUnionFind.point
  let compare = PersistentUnionFind.compare
end)

(* Dealing with the union-find nature of the environment. *)
let same env p1 p2 =
  PersistentUnionFind.same p1 p2 env.state
;;

let get_names (env: env) (point: point): name list =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, _ ->
      names
;;

let names_equal n1 n2 =
  match n1, n2 with
  | User n1, User n2 | Auto n1, Auto n2
    when Variable.equal n1 n2 ->
      true
  | _ ->
      false
;;

let get_kind (env: env) (point: point): kind =
  match PersistentUnionFind.find point env.state with
  | { kind; _ }, _ ->
      kind
;;

(* Merge while keeping the descriptor of the leftmost argument. *)
let merge_left env p2 p1 =
  let open Bash in
  Log.check (get_kind env p1 = get_kind env p2) "Kind mismatch when merging";
  Log.debug "%sMerging%s %a into %a"
    colors.red colors.default
    !internal_pnames (get_names env p1)
    !internal_pnames (get_names env p2);

  (* All this work is just to make sure we keep the names, positions... from
   * both sides. *)
  let state = env.state in
  let { names = names; locations = locations; _ }, _ =
    PersistentUnionFind.find p1 state
  in
  let { names = names'; locations = locations'; _ }, _ =
    PersistentUnionFind.find p2 state
  in
  let names = names @ names' in
  let names = Hml_List.remove_duplicates names in
  let locations = locations @ locations' in
  let locations = Hml_List.remove_duplicates locations in

  (* It is up to the caller to move the permissions if needed... *)
  let state = PersistentUnionFind.update (fun (head, raw) ->
    { head with names; locations }, raw) p2 state
  in
  (* If we don't want to be fancy, the line below is enough. It keeps [p2]. *)
  let env = { env with state = PersistentUnionFind.union p1 p2 state } in
  env
;;

(* Deal with flexible variables that have a structure. *)
let structure (env: env) (point: point): typ option =
  match PersistentUnionFind.find point env.state with
  | { structure = Flexible (Some t); _ }, _ ->
      Some t
  | _ ->
      None
;;

let has_structure env p =
  Option.is_some (structure env p)
;;


(* ---------------------------------------------------------------------------- *)

(* Fact-related functions. *)

let fact_leq f1 f2 =
  match f1, f2 with
  | _, Affine ->
      true
  | _ when f1 = f2 ->
      true
  | _ ->
      false
;;

let fact_of_flag = function
  | SurfaceSyntax.Exclusive ->
      Exclusive
  | SurfaceSyntax.Duplicable ->
      Duplicable [||]
;;


(* ---------------------------------------------------------------------------- *)

(* Fun with de Bruijn indices. *)

exception UnboundPoint

let valid env p =
  PersistentUnionFind.valid p env.state
;;

let repr env p =
  PersistentUnionFind.repr p env.state
;;

let clean top sub t =
  let rec clean t =
    match t with
    (* Special type constants. *)
    | TyUnknown
    | TyDynamic
    | TyEmpty
    | TyVar _ ->
        t

    | TyPoint p ->
        let p = repr sub p in
        if valid top p then
          TyPoint p
        else
          raise UnboundPoint

    | TyForall (b, t) ->
        TyForall (b, clean t)

    | TyExists (b, t) ->
        TyExists (b, clean t)

    | TyApp (t1, t2) ->
        TyApp (clean t1, clean t2)

      (* Structural types. *)
    | TyTuple ts ->
        TyTuple (List.map clean ts)

    | TyConcreteUnfolded (datacon, fields) ->
        let fields = List.map (function
          | FieldValue (f, t) ->
              FieldValue (f, clean t)
          | FieldPermission p ->
              FieldPermission (clean p)
        ) fields in
        TyConcreteUnfolded (datacon, fields)

    | TySingleton t ->
        TySingleton (clean t)

    | TyArrow (t1, t2) ->
        TyArrow (clean t1, clean t2)

    | TyBar (t1, t2) ->
        TyBar (clean t1, clean t2)

    | TyAnchoredPermission (t1, t2) ->
        TyAnchoredPermission (clean t1, clean t2)

    | TyStar (t1, t2) ->
        TyStar (clean t1, clean t2)

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (f, t) -> (f, clean t)) constraints in
        TyConstraints (constraints, clean t)
  in
  clean t
;;

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
        if not (valid env p1) || not (valid env p2) then
          raise UnboundPoint;

        begin match structure env p1, structure env p2 with
        | Some t1, _ ->
            equal t1 t2
        | _, Some t2 ->
            equal t1 t2
        | None, None ->
            same env p1 p2
        end

    | TyExists ((_, k1, _), t1), TyExists ((_, k2, _), t2)
    | TyForall ((_, k1, _), t1), TyForall ((_, k2, _), t2) ->
        k1 = k2 && equal t1 t2

    | TyArrow (t1, t'1), TyArrow (t2, t'2)
    | TyBar (t1, t'1), TyBar (t2, t'2)
    | TyApp (t1, t'1), TyApp (t2, t'2)  ->
        equal t1 t2 && equal t'1 t'2

    | TyTuple ts1, TyTuple ts2 ->
        List.length ts1 = List.length ts2 && List.for_all2 equal ts1 ts2

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

    | TyConstraints (c1, t1), TyConstraints (c2, t2) ->
        List.for_all2 (fun (f1, t1) (f2, t2) ->
          f1 = f2 && equal t1 t2) c1 c2
        && equal t1 t2

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
        TyTuple (List.map (lift i) ts)

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

    | TyBar (t, p) ->
        TyBar (lift i t, lift i p)

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (f, t) -> f, lift i t) constraints in
        TyConstraints (constraints, lift i t)

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
let tsubst (t2: typ) (i: int) (t1: typ) =
  let rec tsubst t2 i t1 =
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
        TyForall (binder, tsubst t2 (i+1) t)

    | TyExists (binder, t) ->
        TyExists (binder, tsubst t2 (i+1) t)

    | TyApp (t, t') ->
        TyApp (tsubst t2 i t, tsubst t2 i t')

    | TyTuple ts ->
        TyTuple (List.map (tsubst t2 i) ts)

    | TyConcreteUnfolded (name, fields) ->
       TyConcreteUnfolded (name, List.map (function
         | FieldValue (field_name, t) -> FieldValue (field_name, tsubst t2 i t)
         | FieldPermission t -> FieldPermission (tsubst t2 i t)) fields)

    | TySingleton t ->
        TySingleton (tsubst t2 i t)

    | TyArrow (t, t') ->
        TyArrow (tsubst t2 i t, tsubst t2 i t')

    | TyAnchoredPermission (p, q) ->
        TyAnchoredPermission (tsubst t2 i p, tsubst t2 i q)

    | TyEmpty ->
        t1

    | TyStar (p, q) ->
        TyStar (tsubst t2 i p, tsubst t2 i q)

    | TyBar (t, p) ->
        TyBar (tsubst t2 i t, tsubst t2 i p)

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (f, t) ->
          f, tsubst t2 i t
        ) constraints in
        TyConstraints (constraints, tsubst t2 i t)
  in
  tsubst t2 i t1
;;

let tsubst_field t2 i = function
  | FieldValue (name, typ) ->
      FieldValue (name, tsubst t2 i typ)
  | FieldPermission typ ->
      FieldPermission (tsubst t2 i typ)
;;

let tsubst_data_type_def_branch t2 i branch =
  let name, fields = branch in
  name, List.map (tsubst_field t2 i) fields
;;


(* ---------------------------------------------------------------------------- *)

(* Various helpers for creating and destructuring [typ]s easily. *)

(* Saves us the trouble of matching all the time. *)
let (!!) = function TyPoint x -> x | _ -> assert false;;
let (!*) = Lazy.force;;
let (>>=) = Option.bind;;
let (|||) o1 o2 = if Option.is_some o1 then o1 else o2 ;;


let ty_equals x =
  TySingleton (TyPoint x)
;;

let ty_unit =
  TyTuple []
;;

let ty_tuple ts =
  TyTuple ts
;;

(* This is right-associative, so you can write [list int @-> int @-> tuple []] *)
let (@->) x y =
  TyArrow (x, y)
;;

let ty_bar t p =
  TyBar (t, p)
;;


let rec flatten_star = function
  | TyStar (p, q) ->
      flatten_star p @ flatten_star q
  | TyEmpty ->
      []
  | TyAnchoredPermission _ as p ->
      [p]
  | _ ->
      Log.error "[flatten_star] only works for types with kind PERM"
;;

let fold_star perms =
  if List.length perms > 0 then
    Hml_List.reduce (fun acc x -> TyStar (acc, x)) perms
  else
    TyEmpty
;;

let strip_forall t =
  let rec strip acc = function
  | TyForall (b, t) ->
      strip (b :: acc) t
  | _ as t ->
      List.rev acc, t
  in
  strip [] t
;;

let fold_forall bindings t =
  List.fold_right (fun binding t ->
    TyForall (binding, t)
  ) bindings t
;;

let fold_exists bindings t =
  List.fold_right (fun binding t ->
    TyExists (binding, t)
  ) bindings t
;;


(* ---------------------------------------------------------------------------- *)

(* Various functions related to binding and finding. *)

let head name location ~flexible kind =
  let structure = if flexible then Flexible None else Rigid in
  {
    names = [name];
    locations = [location];
    binding_mark = Mark.create ();
    structure;
    kind;
  }
;;

let bind_term
    (env: env)
    (name: name)
    (location: location)
    ?(flexible=false)
    ?(include_equals=true)
    (ghost: bool): env * point
  =
  let binding =
    head name location ~flexible KTerm,
    BTerm { permissions = []; ghost }
  in
  let point, state = PersistentUnionFind.create binding env.state in
  let initial_permissions = if include_equals then [ ty_equals point ] else [] in
  let state = PersistentUnionFind.update
    (function
      | (head, BTerm raw) -> head, BTerm { raw with permissions = initial_permissions }
      | _ -> assert false)
    point
    state
  in
  { env with state }, point
;;

let bind_type
    (env: env)
    (name: name)
    (location: location)
    ?(flexible=false)
    ?(definition: type_def option)
    (fact: fact)
    (kind: kind): env * point
  =
  let return_kind, _args = flatten_kind kind in
  Log.check (return_kind = KType) "[bind_type] is for variables with kind TYPE only";
  let binding = head name location ~flexible kind, BType { fact; definition; } in
  let point, state = PersistentUnionFind.create binding env.state in
  { env with state }, point
;;

let bind_var (env: env) ?(flexible=false) ?(fact=Affine) (name, kind, location: type_binding): env * point =
  match kind with
    | KType ->
        (* Of course, such a type variable does not have a definition. *)
        bind_type env name location ~flexible fact kind
    | KTerm ->
        (* This is wrong because we're floating "real" parameters of a function
           as type variables with kind TERM, so it's not a ghost variable... *)
        bind_term env name location ~flexible true
    | KPerm ->
        Log.error "TODO"
    | KArrow _ ->
        Log.error "No arrows expected here"
;;

(* When crossing a binder, say, [a :: TYPE], use this function to properly add
 * [a] in scope. *)
let bind_var_in_type2
    (env: env)
    (binding: type_binding)
    ?(flexible=false)
    (typ: typ): env * typ * point
  =
  let env, point = bind_var env ~flexible binding in
  let typ = tsubst (TyPoint point) 0 typ in
  env, typ, point
;;

let bind_var_in_type
    (env: env)
    (binding: type_binding)
    ?(flexible=false)
    (typ: typ): env * typ
  =
  let env, typ, _ = bind_var_in_type2 env binding ~flexible typ in
  env, typ
;;

let bind_param_at_index_in_data_type_def_branches
    (env: env)
    (name: name)
    (fact: fact)
    (kind: kind)
    (index: index)
    (branches: data_type_def_branch list): env * point * data_type_def_branch list =
  (* This needs a special treatment because the type parameters are not binders
   * per se (unlike TyForall, for instance...). *)
  let env, point = bind_var env ~fact (name, kind, env.location) in
  let branches =
    List.map (tsubst_data_type_def_branch (TyPoint point) index) branches
  in
  env, point, branches
;;

let find_type (env: env) (point: point): name * type_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, BType binding ->
      List.hd names, binding
  | _ ->
      Log.error "Binder %a is not a type" !internal_pnames (get_names env point)
;;

let find_term (env: env) (point: point): name * term_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, BTerm binding ->
      List.hd names, binding
  | _ ->
      Log.error "Binder %a is not a term" !internal_pnames (get_names env point)
;;

let is_type (env: env) (point: point): bool =
  match PersistentUnionFind.find point env.state with
  | _, BType _ ->
      true
  | _ ->
      false
;;

let is_term (env: env) (point: point): bool =
  match PersistentUnionFind.find point env.state with
  | _, BTerm _ ->
      true
  | _ ->
      false
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
          | (head, BType b) -> Some (f head b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map_terms env f =
  Hml_List.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | (head, BTerm b) -> Some (f head b) :: acc
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
  PersistentUnionFind.fold (fun acc k v ->
    f acc k v)
  acc env.state
;;

let fold_terms env f acc =
  PersistentUnionFind.fold (fun acc k (head, binding) ->
    match binding with BTerm b -> f acc k head b | _ -> acc)
  acc env.state
;;

let fold_types env f acc =
  PersistentUnionFind.fold (fun acc k (head, binding) ->
    match binding with BType b -> f acc k head b | _ -> acc)
  acc env.state
;;

let replace env point f =
  { env with state = PersistentUnionFind.update f point env.state }
;;

let replace_term env point f =
  { env with state =
      PersistentUnionFind.update (function
        | names, BTerm b ->
            names, BTerm (f b)
        | _ ->
            Log.error "Not a term"
      ) point env.state
  }
;;

let replace_type env point f =
  { env with state =
      PersistentUnionFind.update (function
        | names, BType b ->
            names, BType (f b)
        | _ ->
            Log.error "Not a type"
      ) point env.state
  }
;;

let refresh_fact env p fact =
  replace_type env p (fun binder -> { binder with fact })
;;


(* Dealing with marks. *)

let is_marked (env: env) (point: point): bool =
  let { binding_mark; _ }, _ = PersistentUnionFind.find point env.state in
  Mark.equals binding_mark env.mark
;;

let mark (env: env) (point: point): env =
  { env with state =
      PersistentUnionFind.update (fun (head, binding) ->
        { head with binding_mark = env.mark }, binding
      ) point env.state
  }
;;

let refresh_mark (env: env): env =
  { env with mark = Mark.create () }
;;

(* A hodge-podge of getters. *)

let get_name env p =
  List.hd (get_names env p)
;;

let get_permissions (env: env) (point: point): permissions =
  let _, { permissions; _ } = find_term env point in
  permissions
;;

let get_fact (env: env) (point: point): fact =
  let _, { fact; _ } = find_type env point in
  fact
;;

let get_locations (env: env) (point: point): location list =
  match PersistentUnionFind.find point env.state with
  | { locations; _ }, _ ->
      locations
;;

let get_location env p =
  List.hd (get_locations env p)
;;

let get_definition (env: env) (point: point): type_def option =
  let _, { definition; _ } = find_type env point in
  definition
;;

let get_arity_for_kind kind =
  let _, tl = flatten_kind kind in
  List.length tl
;;

let get_arity (env: env) (point: point): int =
  get_arity_for_kind (get_kind env point)
;;

let def_for_datacon (env: env) (datacon: Datacon.name): SurfaceSyntax.data_type_flag * data_type_def =
  match DataconMap.find_opt datacon env.type_for_datacon with
  | Some point ->
      let def, _ = Option.extract (get_definition env point) in
      Option.extract def
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let type_for_datacon (env: env) (datacon: Datacon.name): point =
  DataconMap.find datacon env.type_for_datacon
;;

let variance env point i =
  let _, { definition; _ } = find_type env point in
  let variance = snd (Option.extract definition) in
  List.nth variance i
;;

(* What type am I dealing with? *)

let is_flexible (env: env) (point: point): bool =
  match PersistentUnionFind.find point env.state with
  | { structure = Flexible None; _ }, _ ->
      true
  | _ ->
      false
;;

let has_definition (env: env) (point: point): bool =
  match get_definition env point with
  | Some (Some _, _) ->
      true
  | _ ->
      false
;;

(* Instantiating. *)

let instantiate_flexible env p t =
  Log.check (is_flexible env p) "Trying to instantiate a variable that's not flexible";
  Log.debug "Instantiating %a with %a"
    !internal_pnames (get_names env p)
    !internal_ptype (env, t);
  { env with state =
      PersistentUnionFind.update (function
        | head, binding ->
            { head with structure = Flexible (Some t) }, binding
      ) p env.state }
;;

let instantiate_branch branch args =
  let args = List.rev args in
  let branch = Hml_List.fold_lefti (fun i branch arg ->
    tsubst_data_type_def_branch arg i branch) branch args
  in
  branch
;;

let find_and_instantiate_branch
    (env: env)
    (point: point)
    (datacon: Datacon.name)
    (args: typ list): data_type_def_branch =
  let branches = match get_definition env point with
    | Some (Some (_, branches), _) ->
        branches
    | _ ->
        Log.error "This is not a concrete data type."
  in
  let branch =
    List.find
      (fun (datacon', _) -> Datacon.equal datacon datacon')
      branches
  in
  let branch = instantiate_branch branch args in
  branch
;;

(* Misc. *)

let point_by_name (env: env) (name: string): point =
  let module T = struct exception Found of point end in
  try
    fold env (fun () point ({ names; _ }, _binding) ->
      if List.exists (names_equal (User (Variable.register name))) names then
        raise (T.Found point)) ();
    raise Not_found
  with T.Found point ->
    point
;;

(** This function is actually fairly ugly. This is a temporary solution so that
    [TypeChecker] as well as the test files can refer to type constructors
    defined in the file (e.g. int), for type-checking arithmetic expressions, for
    instance... *)
let find_type_by_name env name =
  TyPoint (point_by_name env name)
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

let fold_tyapp cons args =
  List.fold_left (fun t arg -> TyApp (t, arg)) cons args
;;

let bind_datacon_parameters (env: env) (kind: kind) (branches: data_type_def_branch list):
    env * point list * data_type_def_branch list =
  let _return_kind, params = flatten_kind kind in
  let arity = List.length params in
  (* Turn the list of parameters into letters *)
  let letters: string list = Hml_Pprint.name_gen (List.length params) in
  let env, points, branches = Hml_List.fold_left2i (fun i (env, points, branches) letter kind ->
    let letter = Auto (Variable.register letter) in
    let env, point, branches =
      let index = arity - i - 1 in
      bind_param_at_index_in_data_type_def_branches
        env letter (Fuzzy i) kind index branches
    in
    env, point :: points, branches
  ) (env, [], branches) letters params in
  env, List.rev points, branches
;;


(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  open Hml_Pprint

  (* If [f arg] returns a [document], then write [Log.debug "%a" pdoc (f, arg)] *)
  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    PpBuffer.pretty 1.0 Bash.twidth buf (f env)
  ;;

  (* --------------------------------------------------------------------------- *)

  let print_var = function
    | User var ->
        print_string (Variable.print var)
    | Auto var ->
        colors.yellow ^^ print_string (Variable.print var) ^^ colors.default
  ;;

  let pvar buf (var: name) =
    pdoc buf (print_var, var)
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

  let print_names names =
    if List.length names > 0 then
      let names = List.map print_var names in
      let names = List.map (fun x -> colors.blue ^^ x ^^ colors.default) names in
      let names = join (string ", ") names in
      names
    else
      colors.red ^^ string "[no name]" ^^ colors.default
  ;;

  let pnames buf names =
    pdoc buf (print_names, names)
  ;;

  internal_pnames := pnames;;

  let rec print_quantified
      (env: env)
      (q: string)
      (name: name) 
      (kind: SurfaceSyntax.kind)
      (typ: typ) =
    print_string q ^^ lparen ^^ print_var name ^^ space ^^ ccolon ^^ space ^^
    print_kind kind ^^ rparen ^^ dot ^^ jump (print_type env typ)

  and print_point env point =
    match structure env point with
    | Some t ->
        lparen ^^ string "flex→" ^^ print_type env t ^^ rparen
    | _ ->
        if is_flexible env point then
          print_var (get_name env point) ^^ star
        else
          print_var (get_name env point)


  (* TEMPORARY this does not respect precedence and won't insert parentheses at
   * all! *)
  and print_type env = function
    | TyUnknown ->
        string "unknown"

    | TyDynamic ->
        string "dynamic"

    | TyPoint point ->
        print_point env point

    | TyVar i ->
        int i
        (* Log.error "All variables should've been bound at this stage" *)

      (* Special-casing *)
    | TyAnchoredPermission (TyPoint p, TySingleton (TyPoint p')) ->
        let star = if is_flexible env p then star else empty in
        let star' = if is_flexible env p' then star else empty in
        print_names (get_names env p) ^^ star ^^ space ^^ equals ^^ space ^^
        print_names (get_names env p') ^^ star'

    | (TyForall _) as t ->
        let rec strip_bind acc env = function
          | TyForall (binding, t) ->
              let env, t = bind_var_in_type env binding t in
              strip_bind (binding :: acc) env t
          | _ as t ->
              List.rev acc, env, t
        in
        let vars, env, t = strip_bind [] env t in
        let vars = List.map (fun (x, k, _) ->
          if k = KType then
            print_var x
          else
            print_var x ^^ space ^^ colon ^^ colon ^^ space ^^ print_kind k
        ) vars in
        let vars = join (comma ^^ space) vars in
        let vars = lbracket ^^ vars ^^ rbracket in
        vars ^^ space ^^ print_type env t

    | TyExists (((name, kind, _) as binding), typ) ->
        let env, typ = bind_var_in_type env binding typ in
        print_quantified env "∃" name kind typ

    | TyApp (t1, t2) ->
        print_type env t1 ^^ space ^^ print_type env t2

    | TyTuple components ->
        lparen ^^
        join
          (comma ^^ space)
          (List.map (print_type env) components) ^^
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
        print_type env t1 ^^ space ^^ at ^^ space ^^ print_type env t2

    | TyEmpty ->
        string "empty"

    | TyStar (t1, t2) ->
        print_type env t1 ^^ space ^^ string "∗" ^^ space ^^ print_type env t2

    | TyBar (p, q) ->
        lparen ^^ print_type env p ^^ space ^^ bar ^^ space ^^
        print_type env q ^^ rparen

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (f, t) ->
          print_data_type_flag f ^^ space ^^ print_type env t
        ) constraints in
        let constraints = join comma constraints in
        lparen ^^ constraints ^^ rparen ^^ space ^^ equals ^^ rangle ^^ space ^^
        print_type env t

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

  and print_data_type_flag = function
    | SurfaceSyntax.Exclusive ->
        string "exclusive"
    | SurfaceSyntax.Duplicable ->
        string "duplicable"
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let print_fact (fact: fact): document =
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
  let pfact buf (fact: fact) =
    pdoc buf (print_fact, fact)
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
      map_types env (fun { names; kind; _ } { definition; fact; _ } ->
        let name = List.hd names in
        let arity = get_arity_for_kind kind in
        match definition with
        | Some _ ->
            print_fact name false arity fact
        | None ->
            print_fact name true arity fact
      )
    in
    join hardline lines
  ;;
  
  let print_permission_list (env, { permissions; _ }): document =
    (* let permissions = List.filter (function
      TySingleton (TyPoint _) -> false | _ -> true
    ) permissions in *)
    if List.length permissions > 0 then
      let permissions = List.map (print_type env) permissions in
      join (comma ^^ space) permissions
    else
      string "unknown"
  ;;

  let ppermission_list buf (env, point) =
    let _, binder = find_term env point in
    pdoc buf (print_permission_list, (env, binder))
  ;;

  let print_permissions (env: env): document =
    let header =
      let str = "PERMISSIONS:" ^
        (if env.inconsistent then " ⚠ inconsistent ⚠" else "")
      in
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let lines = map_terms env (fun { names; _ } binder ->
      let names = print_names names in
      let perms = print_permission_list (env, binder) in
      names ^^ space ^^ at ^^ space ^^ (nest 2 perms)
    ) in
    let lines = join break1 lines in
    header ^^ (nest 2 (break1 ^^ lines))
  ;;

  let ppermissions buf permissions =
    pdoc buf (print_permissions, permissions)
  ;;

  internal_ppermissions := ppermissions;;

  let ptype buf arg =
    pdoc buf ((fun (env, t) -> print_type env t), arg)
  ;;

  let penv buf (env: env) =
    pdoc buf (print_permissions, env)
  ;;

  internal_ptype := ptype;;

  let print_binders (env: env): document =
    print_string "Γ (unordered) = " ^^
    join
      (semi ^^ space)
      (map env (fun names _ -> join (string " = ") (List.map print_var names)))
  ;;


end

