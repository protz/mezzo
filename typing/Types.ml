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

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of (Field.name * typ)
  | FieldPermission of typ

type data_type_def =
  data_type_def_branch list

type type_def =
  (SurfaceSyntax.data_type_flag * data_type_def) option

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

  (* The current position. *)
  position: Lexing.position * Lexing.position;
}

and binding =
  binding_head * raw_binding

and binding_head = {
  names: Variable.name list;
  structure: structure;
  kind: kind;
  binding_mark: Mark.t;
}

and raw_binding =
  BType of type_binder | BTerm of term_binder | BPerm of perm_binder

and type_binder = {
  (* Definition: if it's a data type (e.g. [list]) there's a definition for it,
   * otherwise it's none. *)
  definition: type_def;
  (* Associated fact. *)
  fact: fact;
}

and term_binder = {
  (* A list of available permissions for that identifier. *)
  permissions: permissions;
  (* A ghost variable has been introduced, say, through [x :: TERM], and does
   * not represent we can compile. *)
  ghost: bool;
}

and perm_binder = {
  (* XXX this is temporary, we still need to think about how we should represent
   * permissions that are not attached to a particular identifier. A simple
   * strategy would be to attach to the environment a list of all points
   * representing PERM binders. *)
  consumed: bool;
}

(* This is not pretty, but we need some of these functions for debugging, and
 * the printer is near the end. *)

let internal_ptype = ref (fun _ -> assert false);;
let internal_pdoc = ref (fun _ -> assert false);;
let internal_pnames = ref (fun _ -> assert false);;

(* The empty environment. *)
let empty_env = {
  type_for_datacon = DataconMap.empty;
  state = PersistentUnionFind.init ();
  mark = Mark.create ();
  position = Lexing.dummy_pos, Lexing.dummy_pos;
}

let locate env position =
  { env with position }
;;

(* Dealing with the union-find nature of the environment. *)
let same env p1 p2 =
  PersistentUnionFind.same p1 p2 env.state
;;

(* Merge while keeping the descriptor of the leftmost argument. *)
let merge_left env p2 p1 =
  (* All this work is just to make sure we keep the names from both sides. *)
  let state = env.state in
  let { names = names; _ }, _ = PersistentUnionFind.find p1 state in
  let { names = names'; _ }, _ = PersistentUnionFind.find p2 state in
  let names = names @ names' in
  let names = Hml_List.remove_duplicates ~equal_func:Variable.equal names in
  let state = PersistentUnionFind.update (fun (head, raw) ->
    { head with names }, raw) p2 state
  in
  (* If we don't want to be fancy, the line below is enough. It keeps [p2]. *)
  { env with state = PersistentUnionFind.union p1 p2 state }
;;

(* Deal with flexible variables that have a structure. *)
let structure (env: env) (point: point): typ option =
  match PersistentUnionFind.find point env.state with
  | { structure = Flexible (Some t); _ }, _ ->
      Some t
  | _ ->
      None
;;

(* ---------------------------------------------------------------------------- *)

(* Fact-related functions. *)

let fact_leq f1 f2 =
  match f1, f2 with
  | _, Affine ->
      true
  | _ ->
      false
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
        begin match structure env p1, structure env p2 with
        | Some t1, Some t2 ->
            equal t1 t2
        | None, None ->
            same env p1 p2
        | _ ->
            false
        end

    | TyExists ((_, k1), t1), TyExists ((_, k2), t2)
    | TyForall ((_, k1), t1), TyForall ((_, k2), t2) ->
        k1 = k2 && equal t1 t2

    | TyArrow (t1, t'1), TyArrow (t2, t'2)
    | TyApp (t1, t'1), TyApp (t2, t'2)  ->
        equal t1 t2 && equal t'1 t'2

    | TyTuple ts1, TyTuple ts2 ->
        List.for_all2 equal ts1 ts2

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


(* ---------------------------------------------------------------------------- *)

(* Various functions related to binding and finding. *)

let head name ~flexible kind =
  let structure = if flexible then Flexible None else Rigid in
  {
    names = [name];
    binding_mark = Mark.create ();
    structure;
    kind;
  }
;;

let fold_star perms =
  if List.length perms > 0 then
    Hml_List.reduce (fun acc x -> TyStar (acc, x)) perms
  else
    TyEmpty
;;

let bind_term
    (env: env)
    (name: Variable.name)
    ?(flexible=false)
    (ghost: bool): env * point
  =
  let binding =
    head name ~flexible KTerm,
    BTerm { permissions = []; ghost }
  in
  let point, state = PersistentUnionFind.create binding env.state in
  let state = PersistentUnionFind.update
    (function
      | (head, BTerm raw) -> head, BTerm { raw with permissions = [ ty_equals point ] }
      | _ -> assert false)
    point
    state
  in
  { env with state }, point
;;

let bind_type
    (env: env)
    (name: Variable.name)
    ?(flexible=false)
    ?(definition: type_def)
    (fact: fact)
    (kind: kind): env * point
  =
  let return_kind, _args = flatten_kind kind in
  Log.check (return_kind = KType) "[bind_type] is for variables with kind TYPE only";
  let binding = head name ~flexible kind, BType { fact; definition; } in
  let point, state = PersistentUnionFind.create binding env.state in
  { env with state }, point
;;

let bind_var (env: env) ?(flexible=false) (name, kind: type_binding): env * point =
  let fact = Affine in
  match kind with
    | KType ->
        (* Of course, such a type variable does not have a definition. *)
        bind_type env name ~flexible fact kind
    | KTerm ->
        bind_term env name ~flexible true
    | KPerm ->
        Log.error "TODO"
    | KArrow _ ->
        Log.error "No arrows expected here"
;;

(* When crossing a binder, say, [a :: TYPE], use this function to properly add
 * [a] in scope. *)
let bind_var_in_type
    (env: env)
    (binding: type_binding)
    ?(flexible=false)
    (typ: typ): env * typ
  =
  let env, point = bind_var env ~flexible binding in
  let typ = tsubst (TyPoint point) 0 typ in
  env, typ
;;

let bind_param_at_index_in_data_type_def_branches
    (env: env)
    (name: Variable.name)
    (fact: fact)
    (kind: kind)
    (index: index)
    (branches: data_type_def_branch list): env * data_type_def_branch list =
  (* This needs a special treatment because the type parameters are not binders
   * per se (unlike TyForall, for instance...). *)
  let env, point = bind_type env name fact kind in
  let branches =
    List.map (tsubst_data_type_def_branch (TyPoint point) index) branches
  in
  env, branches
;;

let find_type (env: env) (point: point): Variable.name * type_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, BType binding ->
      List.hd names, binding
  | _ ->
      Log.error "Binder is not a type"
;;

let find_term (env: env) (point: point): Variable.name * term_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, BTerm binding ->
      List.hd names, binding
  | _ ->
      Log.error "Binder is not a term"
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

(* A hodge-podge of getters. *)

let get_names (env: env) (point: point): Variable.name list =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, _ ->
      names
;;

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

let get_kind (env: env) (point: point): kind =
  match PersistentUnionFind.find point env.state with
  | { kind; _ }, _ ->
      kind
;;

let get_definition (env: env) (point: point): type_def =
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
      Option.extract (get_definition env point)
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
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
  | Some _ ->
      true
  | _ ->
      false
;;

(* Instantiating. *)

let instantiate_flexible env p t =
  Log.check (is_flexible env p) "Trying to instantiate a variable that's not flexible";
  Log.debug "Instantiating %a with %a"
    !internal_pnames (get_names env p)
    !internal_pdoc (!internal_ptype, (env, t));
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
  let _flag, branches = Option.extract (get_definition env point) in
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
      if List.exists (fun name' -> Variable.(equal (register name) name')) names then
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
        env letter (Fuzzy i) kind index branches
    in
    env, branches
  ) (env, branches) letters params in
  env, branches
;;


(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  open Hml_Pprint

  (* If [f arg] returns a [document], then write [Log.debug "%a" pdoc (f, arg)] *)
  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    PpBuffer.pretty 1.0 Bash.twidth buf (f env)
  ;;

  internal_pdoc := pdoc;;

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

  and print_point env point =
    match structure env point with
    | Some t ->
        lparen ^^ string "f=" ^^ print_type env t ^^ rparen
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
        print_point env p ^^ space ^^ equals ^^ space ^^ print_point env p'

    | TyForall (((name, kind) as binding), typ) ->
        let env, typ = bind_var_in_type env binding typ in
        print_quantified env "∀" name kind typ

    | TyExists (((name, kind) as binding), typ) ->
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
    let permissions = List.map (print_type env) permissions in
    (*let exclusive = List.map
      (fun doc -> colors.underline ^^ doc ^^ colors.default) exclusive
    in*)
    join (comma ^^ space) permissions
  ;;

  let print_names names =
    if List.length names > 0 then
      let names = List.map print_var names in
      let names = List.map (fun x -> colors.blue ^^ x ^^ colors.default) names in
      let names = join (string " a.k.a. ") names in
      names
    else
      colors.red ^^ string "[no name]" ^^ colors.default
  ;;

  let pnames buf names =
    pdoc buf (print_names, names)
  ;;

  internal_pnames := pnames;;

  let print_permissions (env: env): document =
    let header =
      let str = "PERMISSIONS:" in
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let lines = map_terms env (fun { names; _ } binder ->
      let names = print_names names in
      let perms = print_permission_list (env, binder) in
      names ^^ colon ^^ space ^^ (nest 2 perms)
    ) in
    let lines = join break1 lines in
    header ^^ (nest 2 (break1 ^^ lines))
  ;;

  let ptype (env, t) =
    print_type env t
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

