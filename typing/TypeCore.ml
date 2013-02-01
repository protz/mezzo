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
type name = User of Module.name * Variable.name | Auto of Variable.name

let is_user = function User _ -> true | Auto _ -> false;;

type location = Lexing.position * Lexing.position

type type_binding =
  name * kind * location

type flavor = SurfaceSyntax.binding_flavor = CanInstantiate | CannotInstantiate

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

  (* The name of the current unit. *)
  module_name: Module.name;

  (* These permissions are abstract KPerm variables, they're not attached to any
   * point in particular, so we keep a list of them here. *)
  floating_permissions: point list;
}

and binding =
  binding_head * raw_binding

and binding_head = {
  (* This information is only for printing and debugging. *)
  names: name list;
  locations: location list;

  (* Is this a flexible variable, and has it been unified with something? *)
  structure: structure;

  (* The kind of this variable. If kind is KTerm, then the [raw_binding] is a
   * [term_binder]. *)
  kind: kind;

  (* For some passes, we need to mark points as visited. This module provides a
   * set of functions to deal with marks. *)
  binding_mark: Mark.t;
}

and raw_binding =
  BType of type_binder | BTerm of term_binder

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

  (* A ghost variable has been introduced, say, through [x : term], and does
   * not represent something we can compile.
   *
   * TEMPORARY: as of 2012/07/12 this information is not accurate and one should
   * not rely on it. *)
  ghost: bool;
}

(* This is not pretty, but we need some of these functions for debugging, and
 * the printer is near the end. *)

let (^=>) x y = x && y || not x;;

let internal_ptype: (Buffer.t -> (env * typ) -> unit) ref = ref (fun _ -> assert false);;
let internal_pnames: (Buffer.t -> (env * name list) -> unit) ref = ref (fun _ -> assert false);;
let internal_ppermissions: (Buffer.t -> env -> unit) ref = ref (fun _ -> assert false);;
let internal_pfact: (Buffer.t -> fact -> unit) ref = ref (fun _ -> assert false);;

(* The empty environment. *)
let empty_env = {
  type_for_datacon = DataconMap.empty;
  state = PersistentUnionFind.init ();
  mark = Mark.create ();
  location = Lexing.dummy_pos, Lexing.dummy_pos;
  inconsistent = false;
  module_name = Module.register "<none>";
  floating_permissions = [];
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
  | Auto n1, Auto n2 when Variable.equal n1 n2 ->
      true
  | User (m1, n1), User (m2, n2) when Variable.equal n1 n2 && Module.equal m1 m2 ->
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
  (* Debug *)
  let open Bash in
  Log.check (get_kind env p1 = get_kind env p2) "Kind mismatch when merging";
  Log.debug ~level:5 "%sMerging%s %a into %a"
    colors.red colors.default
    !internal_pnames (env, get_names env p1)
    !internal_pnames (env, get_names env p2);

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

  (* More debug *)
  begin match _b1, _b2 with
  | BType { fact = f1; _ }, BType { fact = f2; _ } ->
      Log.debug ~level:6 "→ facts: merging %a into %a"
        !internal_pfact f1 !internal_pfact f2;
  | _ ->
      ()
  end;

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
