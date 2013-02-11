(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)

type db_index =
  int

type point =
  PersistentUnionFind.point

type flex_index =
  int

type kind = SurfaceSyntax.kind = 
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

(** Has this name been auto-generated or not? *)
type name = User of Module.name * Variable.name | Auto of Variable.name

type location = Lexing.position * Lexing.position

type type_binding =
  name * kind * location

type flavor = SurfaceSyntax.binding_flavor = CanInstantiate | CannotInstantiate

module DataconMap = Hml_Map.Make(struct
  type t = Module.name * Datacon.name
  let compare = Pervasives.compare
end)

(* Record fields remain named. *)

module Field = Variable

type variance = Invariant | Covariant | Contravariant | Bivariant

type typ =
    (* Special type constants. *)
  | TyUnknown
  | TyDynamic

    (* We adopt a locally nameless style. Local names are [TyBound]s, global
     * names are [TyOpen]. *)
  | TyBound of db_index
  | TyOpen of var

    (* Quantification and type application. *)
  | TyForall of (type_binding * flavor) * typ
  | TyExists of type_binding * typ
  | TyApp of typ * typ list

    (* Structural types. *)
  | TyTuple of typ list
  | TyConcreteUnfolded of resolved_datacon * data_field_def list * typ
      (* [typ] is for the type of the adoptees; initially it's bottom and then
       * it gets instantiated to something more precise. *)

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
  | TyAnd of duplicity_constraint list * typ
  | TyImply of duplicity_constraint list * typ

and var =
  | VRigid of point
  | VFlexible of flex_index

(* Since data constructors are now properly scoped, they are resolved, that is,
 * they are either attached to a point, or a De Bruijn index, which will later
 * resolve to a point when we open the corresponding type definition. That way,
 * we can easily jump from a data constructor to the corresponding type
 * definition. *)
and resolved_datacon = typ * Datacon.name

and duplicity_constraint = SurfaceSyntax.data_type_flag * typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of (Field.name * typ)
  | FieldPermission of typ

type adopts_clause =
  (* option here because not all concrete types adopt someone *)
  typ option

type data_type_def =
  data_type_def_branch list

type type_def =
  (* option here because abstract types do not have a definition *)
    (SurfaceSyntax.data_type_flag * data_type_def * adopts_clause) option
  * variance list

type data_type_group =
  (Variable.name * location * type_def * fact * kind) list

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
and fact = Exclusive | Duplicable of bitmap | Affine | Fuzzy of int

(* The 0-th element is the first parameter of the type, and the value is true if
  * it has to be duplicable for the type to be duplicable. *)
and bitmap = bool array

type binding_type = Rigid | Flexible

type permissions = typ list

type level = int

(** This is the environment that we use throughout HaMLeT. *)
type env = {
  (* This maps global names (i.e. [TyOpen]s) to their corresponding binding. *)
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

  (* The name of the current unit. *)
  module_name: Module.name;

  (* This is a list of abstract permissions available in the environment. It can
   * either be a type application, i.e. "p x", where "p" is abstract, or a type
   * variable. They're not attached to any point in particular, so we keep a
   * list of them here. *)
  floating_permissions: typ list;

  (* We need to bump the level when introducing a rigid binding after a flexible
   * one. *)
  last_binding: binding_type;

  (* We also need to store the current level. *)
  current_level: level;

  (* The list of flexible bindings. *)
  flexible: flex_descr list;
}

and flex_descr = {
  (* If a flexible variable is not instanciated, it has a descriptor. When it
   * becomes instantiated, it loses its descriptor and gains the information
   * from another type. We have the invariant that importants properties about
   * the variable (fact, level, kind) are "better" after it lost its descriptor
   * (more precise fact, lower level, equal kind). *)
  structure: structure;
}

and structure = NotInstantiated of var_descr | Instantiated of typ

and binding = var_descr * extra_descr

(** This contains all sorts of useful information about a type variable. *)
and var_descr = {
  (* This information is only for printing and debugging. *)
  names: name list;
  locations: location list;

  (* The kind of this variable. If kind is KTerm, then the [raw_binding] is a
   * [term_binder]. *)
  kind: kind;

  (* For some passes, we need to mark points as visited. This module provides a
   * set of functions to deal with marks. *)
  binding_mark: Mark.t;

  (* Associated fact. Variables with kind type have an associated fact; others
   * don't. *)
  fact: fact option;

  (* Associated level. *)
  level: level;
}

and extra_descr = DType of type_descr | DTerm of term_descr | DNone

and type_descr = {
  (* This is the descriptor for a data type definition / abstract type
   * definition. *)
  definition: type_def;
}

and term_descr = {
  (* A list of available permissions for that identifier. *)
  permissions: permissions;

  (* A ghost variable has been introduced, say, through [x : term], and does
   * not represent something we can compile.
   *
   * TEMPORARY: as of 2012/07/12 this information is not accurate and one should
   * not rely on it. *)
  ghost: bool;
}

(* This is not pretty, but we need some of these functions for debugging, and
 * the printer is near the end. *)

let internal_ptype: (Buffer.t -> (env * typ) -> unit) ref = ref (fun _ -> assert false);;
let internal_pnames: (Buffer.t -> (env * name list) -> unit) ref = ref (fun _ -> assert false);;
let internal_ppermissions: (Buffer.t -> env -> unit) ref = ref (fun _ -> assert false);;
let internal_pfact: (Buffer.t -> fact -> unit) ref = ref (fun _ -> assert false);;

(* The empty environment. *)
let empty_env = {
  state = PersistentUnionFind.init ();
  mark = Mark.create ();
  location = Lexing.dummy_pos, Lexing.dummy_pos;
  inconsistent = false;
  module_name = Module.register "<none>";
  floating_permissions = [];
  last_binding = Rigid;
  current_level = 0;
  flexible = [];
}

let locate env location =
  { env with location }
;;

let location { location; _ } = location;;

let is_inconsistent { inconsistent; _ } = inconsistent;;

let mark_inconsistent env = { env with inconsistent = true };;

let module_name { module_name; _ } = module_name;;

let set_module_name env module_name = { env with module_name };;

let valid env p =
  PersistentUnionFind.valid p env.state
;;

let repr env p =
  PersistentUnionFind.repr p env.state
;;

let find env p =
  PersistentUnionFind.find p env.state
;;

(* ---------------------------------------------------------------------------- *)

(** Dealing with flexible variables. Flexible variables are not stored in the
 * persistent union-find: they're stored in a separate list. *)

(* Given the index of a flexible variable, find its corresponding descriptor. *)
let find_flex (env: env) (f: flex_index): flex_descr =
  List.nth env.flexible f 
;;

(* Replace the descriptor of a flexible variable with another one. *)
let replace_flex (env: env) (f: flex_index) (d: flex_descr): env =
  let flexible = List.mapi (fun i d' -> if i = f then d else d') env.flexible in
  { env with flexible }
;;

exception UnboundPoint

(* Goes through any flexible variables before finding "the real type". *)
let rec modulo_flex_v (env: env) (v: var): typ =
  match v with
  | VRigid p ->
      if valid env p then
        TyOpen (VRigid (repr env p))
      else
        raise UnboundPoint
  | VFlexible f ->
      if f < List.length env.flexible then
        match (find_flex env f).structure with
        | Instantiated (TyOpen v) ->
            modulo_flex_v env v
        | Instantiated t ->
            t
        | NotInstantiated _ ->
            TyOpen v
      else
        raise UnboundPoint
;;

(* Same thing with a type. *)
let modulo_flex (env: env) (t: typ): typ =
  match t with
  | TyOpen v -> modulo_flex_v env v
  | _ -> t
;;

(* Is this variable flexible? (i.e. can I call "instantiate_flexible" on it? *)
let is_flexible (env: env) (v: var): bool =
  match modulo_flex_v env v with
  | TyOpen (VFlexible _) ->
      true
  | _ ->
      false
;;

(* This is where all the safety checks will happen. *)
let can_instantiate (env: env) (v: var) (t: typ): bool =
  ignore t;
  is_flexible env v &&
  (* FIXME check facts, assert kinds, levels *)
  true
;;

let import_flex_instanciations env sub_env =
  { env with flexible = Hml_List.cut (List.length env.flexible) sub_env.flexible }
;;



(* ---------------------------------------------------------------------------- *)

(** Some functions that operate on variables. *)

let assert_var env v =
  match modulo_flex_v env v with
  | TyOpen v ->
      v
  | _ ->
      Log.error "[assert_var] failed"
;;

let assert_point env v =
  match modulo_flex_v env v with
  | TyOpen (VRigid p) ->
      p
  | _ ->
      Log.error "[assert_point] failed"
;;

let update_extra_descr (env: env) (var: var) (f: extra_descr -> extra_descr): env =
  let point = assert_point env var in
  { env with state =
    PersistentUnionFind.update (fun (var_descr, extra_descr) ->
      var_descr, f extra_descr
    ) point env.state
  }
;;

let get_var_descr (env: env) (v: var): var_descr =
  match assert_var env v with
  | VFlexible f ->
      begin match (find_flex env f).structure with
      | NotInstantiated descr ->
          descr
      | Instantiated _ ->
          assert false
      end
  | VRigid p ->
      let var_descr, _extra_descr = PersistentUnionFind.find p env.state in
      var_descr
;;

let update_var_descr (env: env) (v: var) (f: var_descr -> var_descr): env =
  match assert_var env v with
  | VFlexible i ->
      replace_flex env i (
        match find_flex env i with
        | { structure = NotInstantiated descr } ->
            { structure = NotInstantiated (f descr) }
        | { structure = Instantiated _ } ->
            assert false
      )
  | VRigid p ->
      {
        env with state =
          PersistentUnionFind.update (fun (var_descr, extra_descr) ->
            (f var_descr), extra_descr)
          p
          env.state
      }
;;
 
let initial_permissions_for_point point =
  [ TySingleton (TyOpen (VRigid point)); TyUnknown ]
;;

let get_permissions (env: env) (var: var): permissions =
  let point = assert_point env var in
  match find env point with
  | _, DTerm { permissions; _ } ->
      permissions
  | _ ->
      assert false
;;

let set_permissions (env: env) (var: var) (permissions: typ list): env =
  update_extra_descr env var (function
    | DTerm term ->
        DTerm { term with permissions }
    | _ ->
        Log.error "Not a term"
  )
;;

let reset_permissions (env: env) (var: var): env =
  let point = assert_point env var in
  update_extra_descr env var (function
    | DTerm term ->
        DTerm { term with permissions = initial_permissions_for_point point }
    | _ ->
        Log.error "Not a term"
  )
;;

let get_fact (env: env) (var: var): fact =
  Option.extract (get_var_descr env var).fact
;;

let get_locations (env: env) (var: var): location list =
  (get_var_descr env var).locations
;;

let add_location (env: env) (var: var) (loc: location): env =
  update_var_descr env var (fun var_descr ->
    { var_descr with locations = loc :: var_descr.locations }
  )
;;

let get_names (env: env) (var: var): name list =
  (get_var_descr env var).names
;;

let get_definition (env: env) (var: var): type_def option =
  match var with
  | VFlexible _ ->
      None
  | VRigid point ->
      match find env point with
      | _, DType { definition; _ } ->
          Some definition
      | _ ->
          None
;;

let update_definition (env: env) (var: var) (f: type_def -> type_def): env =
  update_extra_descr env var (function
    | DType { definition } ->
        DType { definition = f definition }
    | _ ->
        Log.error "Refining the definition of a type that didn't have one in the first place"
  )
;;

let set_definition (env: env) (var: var) (definition: type_def): env =
  update_extra_descr env var (function
    | DNone ->
        DType { definition }
    | _ ->
        Log.error "Setting the definition of a type that had one in the first place"
  )
;;

let get_kind (env: env) (var: var): kind =
  (get_var_descr env var).kind
;;

let set_fact (env: env) (var: var) (fact: fact): env =
  let fact = Some fact in
  update_var_descr env var (fun d -> { d with fact })
;;

let get_floating_permissions { floating_permissions; _ } =
  floating_permissions
;;

let set_floating_permissions env floating_permissions =
  { env with floating_permissions }
;;

(* ---------------------------------------------------------------------------- *)

(* Instantiate a flexible variable with a given type. *)
let instantiate_flexible (env: env) (v: var) (t: typ): env =
  Log.check (is_flexible env v) "[instantiate_flex] wants flexible";
  Log.debug "Instantiating %a with %a"
    !internal_pnames (env, get_names env v)
    !internal_ptype (env, t);

  match modulo_flex_v env v with
  | TyOpen (VFlexible f) ->
      replace_flex env f { structure = Instantiated t }
  | _ ->
      assert false
;;

(* ---------------------------------------------------------------------------- *)

(** Some functions related to the manipulation of the union-find structure of
 * the environment. *)

module VarMap = Hml_Map.Make(struct
  type t = var
  let compare x y =
    match x, y with
    | VRigid x, VRigid y ->
        PersistentUnionFind.compare x y
    | _ ->
        Log.error "[VarMap] used in the presence of flexible variables"
end)

(* Dealing with the union-find nature of the environment. *)
let same env v1 v2 =
  match assert_var env v1, assert_var env v2 with
  | VRigid p1, VRigid p2 ->
      PersistentUnionFind.same p1 p2 env.state
  | VFlexible f1, VFlexible f2 ->
      f1 = f2
  | _ ->
      false
;;

(* Merge while keeping the descriptor of the leftmost argument. *)
let merge_left_p2p env p2 p1 =
 (* All this work is just to make sure we keep the names, positions... from
   * both sides. *)
  let state = env.state in
  let { names = names; locations = locations; _ }, _b1 =
    PersistentUnionFind.find p1 state
  in
  let { names = names'; locations = locations'; _ }, _b2 =
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

let merge_left env v1 v2 =
  let v1 = assert_var env v1 in
  let v2 = assert_var env v2 in

  (* Sanity check. *)
  Log.check (get_kind env v1 = get_kind env v2) "Kind mismatch when merging";

  (* Debug *)
  let open Bash in
  Log.debug ~level:5 "%sMerging%s %a into %a"
    colors.red colors.default
    !internal_pnames (env, get_names env v1)
    !internal_pnames (env, get_names env v2);
  if get_kind env v1 = KType then
    Log.debug ~level:6 "→ facts: merging %a into %a"
      !internal_pfact (get_fact env v1)
      !internal_pfact (get_fact env v2);

 
  match v1, v2 with
  | VRigid p1, VRigid p2 ->
      merge_left_p2p env p1 p2
  | (VRigid _ as v), (VFlexible _ as vf)
  | (VFlexible _ as vf), (VRigid _ as v) ->
      if can_instantiate env vf (TyOpen v) then
        instantiate_flexible env vf (TyOpen v)
      else
        env
  | VFlexible i, VFlexible j ->
      if i < j then
        instantiate_flexible env v2 (TyOpen v1)
      else
        instantiate_flexible env v1 (TyOpen v2)
;;


(* ---------------------------------------------------------------------------- *)


let clean top sub t =
  let rec clean t =
    match t with
    (* Special type constants. *)
    | TyUnknown
    | TyDynamic
    | TyEmpty
    | TyBound _ ->
        t

    | TyOpen (VRigid p) ->
        let p = repr sub p in
        if valid top p then
          TyOpen (VRigid p)
        else
          raise UnboundPoint

    | TyOpen (VFlexible f) ->
        if f <= top.current_level then
          match (find_flex sub f).structure with
          | Instantiated t ->
              clean t
          | NotInstantiated _ ->
              t
        else
          raise UnboundPoint

    | TyForall (b, t) ->
        TyForall (b, clean t)

    | TyExists (b, t) ->
        TyExists (b, clean t)

    | TyApp (t1, t2) ->
        TyApp (clean t1, List.map clean t2)

      (* Structural types. *)
    | TyTuple ts ->
        TyTuple (List.map clean ts)

    | TyConcreteUnfolded ((t, dc), fields, clause) ->
        let t = clean t in
        let fields = List.map (function
          | FieldValue (f, t) ->
              FieldValue (f, clean t)
          | FieldPermission p ->
              FieldPermission (clean p)
        ) fields in
        TyConcreteUnfolded ((t, dc), fields, clean clause)

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

    | TyAnd (constraints, t) ->
        let constraints = List.map (fun (f, t) -> (f, clean t)) constraints in
        TyAnd (constraints, clean t)

    | TyImply (constraints, t) ->
        let constraints = List.map (fun (f, t) -> (f, clean t)) constraints in
        TyImply (constraints, clean t)
  in
  clean t
;;

let valid env = function
  | VFlexible _ as v ->
      (get_var_descr env v).level <= env.current_level
  | VRigid p ->
      valid env p
;;

let rec resolved_datacons_equal env (t1, dc1) (t2, dc2) =
  equal env t1 t2 && Datacon.equal dc1 dc2

(* [equal env t1 t2] provides an equality relation between [t1] and [t2] modulo
 * equivalence in the [PersistentUnionFind]. *)
and equal env (t1: typ) (t2: typ) =
  let rec equal (t1: typ) (t2: typ) =
    match modulo_flex env t1, modulo_flex env t2 with
      (* Special type constants. *)
    | TyUnknown, TyUnknown
    | TyDynamic, TyDynamic ->
        true

    | TyBound i, TyBound i' ->
        i = i'

    | TyOpen p1, TyOpen p2 ->
        if not (valid env p1) || not (valid env p2) then
          raise UnboundPoint;

        same env p1 p2

    | TyExists ((_, k1, _), t1), TyExists ((_, k2, _), t2)
    | TyForall (((_, k1, _), _), t1), TyForall (((_, k2, _), _), t2) ->
        k1 = k2 && equal t1 t2

    | TyArrow (t1, t'1), TyArrow (t2, t'2)
    | TyBar (t1, t'1), TyBar (t2, t'2) ->
        equal t1 t2 && equal t'1 t'2

    | TyApp (t1, t'1), TyApp (t2, t'2)  ->
        equal t1 t2 && List.for_all2 equal t'1 t'2

    | TyTuple ts1, TyTuple ts2 ->
        List.length ts1 = List.length ts2 && List.for_all2 equal ts1 ts2

    | TyConcreteUnfolded (name1, fields1, clause1), TyConcreteUnfolded (name2, fields2, clause2) ->
        resolved_datacons_equal env name1 name2 &&
        equal clause1 clause2 &&
        List.length fields1 = List.length fields2 &&
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

    | TyAnd (c1, t1), TyAnd (c2, t2) ->
        List.for_all2 (fun (f1, t1) (f2, t2) ->
          f1 = f2 && equal t1 t2) c1 c2
        && equal t1 t2

    | TyImply (c1, t1), TyImply (c2, t2) ->
        List.for_all2 (fun (f1, t1) (f2, t2) ->
          f1 = f2 && equal t1 t2) c1 c2
        && equal t1 t2

    | _ ->
        false
  in
  equal t1 t2
;;



(* ---------------------------------------------------------------------------- *)

(* Binding, finding, iterating. *)

let mkdescr env name kind location fact =
  let var_descr = {
    names = [name];
    locations = [location];
    kind;
    fact;
    binding_mark = Mark.create ();
    level = env.current_level;
  } in
  var_descr
;;

let mkfact k =
  match k with
  | KTerm ->
      None
  | _ ->
      Some Affine
;;

let bind_rigid env (name, kind, location) =
  (* Deal with levels. *)
  let env =
    match env.last_binding with
    | Flexible ->
        { env with current_level = env.current_level + 1; last_binding = Rigid }
    | Rigid ->
        env
  in

  (* Prepare the descriptor. *)
  let var_descr = mkdescr env name kind location (mkfact kind) in
  let descr = var_descr, DNone in

  (* Register the descriptors in the union-find, update the list of permissions
   * if needed. *)
  let point, state = PersistentUnionFind.create descr env.state in
  let extra_descr =
    match kind with
    | KTerm ->
        DTerm { permissions = initial_permissions_for_point point; ghost = false }
    | _ ->
        DNone
  in
  let state = PersistentUnionFind.update (fun _ -> var_descr, extra_descr) point state in

  { env with state }, VRigid point
;;


let bind_flexible env (name, kind, location) =
  (* Deal with levels. No need to bump the level here. *)
  let env = { env with last_binding = Flexible } in

  (* Create the descriptor *)
  let var_descr = mkdescr env name kind location (mkfact kind) in

  (* Our (future) index in the list *)
  let f = List.length env.flexible in

  (* Create the flexible descriptor, add it to our list of flexible variables. *)
  let flex_descr = { structure = NotInstantiated var_descr } in
  (* FIXME reverse the list *)
  let env = { env with flexible = env.flexible @ [flex_descr] } in

  env, VFlexible f
;;


(* ---------------------------------------------------------------------------- *)

(* Iterating on rigid variables. *)

let internal_fold env f acc =
  PersistentUnionFind.fold (fun acc k v ->
    f acc k v)
  acc env.state
;;

let fold env f acc =
  PersistentUnionFind.fold
    (fun acc point _ -> f acc (VRigid point))
    acc
    env.state
;;

let fold_terms env f acc =
  PersistentUnionFind.fold (fun acc point (_, extra_descr) ->
    match extra_descr with DTerm { permissions; _ } -> f acc (VRigid point) permissions | _ -> acc)
  acc env.state
;;

let fold_definitions env f acc =
  PersistentUnionFind.fold (fun acc point (_, extra_descr) ->
    match extra_descr with DType { definition } -> f acc (VRigid point) definition | _ -> acc)
  acc env.state
;;

let map env f =
  fold env (fun acc var -> f var :: acc) []
;;

(* ---------------------------------------------------------------------------- *)

(* Interface-related functions. *)

(* Get all the names from module [mname] found in [env]. *)
let get_exports env mname =
  let assoc =
    internal_fold env (fun acc point ({ names; kind; _ }, _) ->
      let canonical_names = Hml_List.map_some (function
        | User (m, x) when Module.equal m mname ->
            Some (x, kind)
        | _ ->
            None
      ) names in
      List.map (fun (x, k) -> x, k, VRigid point) canonical_names :: acc
    ) []
  in
  List.flatten assoc
;;

let names_equal n1 n2 =
  match n1, n2 with
  | Auto n1, Auto n2 when Variable.equal n1 n2 ->
      true
  | User (m1, n1), User (m2, n2) when Variable.equal n1 n2 && Module.equal m1 m2 ->
      true
  | _ ->
      false
;;

let point_by_name (env: env) ?(mname: Module.name option) (name: Variable.name): var =
  let mname = Option.map_none env.module_name mname in
  let module T = struct exception Found of point end in
  try
    internal_fold env (fun () point ({ names; _ }, _binding) ->
      if List.exists (names_equal (User (mname, name))) names then
        raise (T.Found point)) ();
    raise Not_found
  with T.Found point ->
    VRigid point
;;

(* ---------------------------------------------------------------------------- *)

(* Dealing with marks. *)

let is_marked (env: env) (var: var): bool =
  let { binding_mark; _ } = get_var_descr env var in
  Mark.equals binding_mark env.mark
;;

let mark (env: env) (var: var): env =
  update_var_descr env var (fun descr -> { descr with binding_mark = env.mark })
;;

let refresh_mark (env: env): env =
  { env with mark = Mark.create () }
;;

(* ---------------------------------------------------------------------------- *)

let internal_uniqvarid env = function
  | VFlexible i ->
      i lsl 16
  | VRigid point ->
      let p = PersistentUnionFind.repr point env.state in
      (Obj.magic p: int)
;;

