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

open TypeCore

(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

(* Fun with de Bruijn indices. *)

let lift (k: int) (t: typ) =
  let rec lift (i: int) (t: typ) =
    match t with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic ->
        t

    | TyBound j ->
        if j < i then
          TyBound j
        else
          TyBound (j + k)

    | TyOpen _ ->
        t

    | TyForall (binder, t) ->
        TyForall (binder, lift (i+1) t)

    | TyExists (binder, t) ->
        TyExists (binder, lift (i+1) t)

    | TyApp (t1, t2) ->
        TyApp (lift i t1, List.map (lift i) t2)

    | TyTuple ts ->
        TyTuple (List.map (lift i) ts)

    | TyConcreteUnfolded ((t, dc), fields, clause) ->
        TyConcreteUnfolded (
          (lift i t, dc),
          List.map (function
            | FieldValue (field_name, t) -> FieldValue (field_name, lift i t)
            | FieldPermission t -> FieldPermission (lift i t)) fields,
          lift i clause
        )

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

    | TyAnd (constraints, t) ->
        let constraints = List.map (fun (f, t) -> f, lift i t) constraints in
        TyAnd (constraints, lift i t)

    | TyImply (constraints, t) ->
        let constraints = List.map (fun (f, t) -> f, lift i t) constraints in
        TyImply (constraints, lift i t)

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
 * expected not to have any free [TyBound]s: they've all been converted to
 * [TyOpen]s. Therefore, [t2] will *not* be lifted when substituted for [i] in
 * [t1]. *)
let tsubst (t2: typ) (i: int) (t1: typ) =
  let rec tsubst t2 i t1 =
    match t1 with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic ->
        t1

    | TyBound j ->
        if j = i then
          t2
        else
          TyBound j

    | TyOpen _ ->
        t1

    | TyForall (binder, t) ->
        TyForall (binder, tsubst t2 (i+1) t)

    | TyExists (binder, t) ->
        TyExists (binder, tsubst t2 (i+1) t)

    | TyApp (t, t') ->
        TyApp (tsubst t2 i t, List.map (tsubst t2 i) t')

    | TyTuple ts ->
        TyTuple (List.map (tsubst t2 i) ts)

    | TyConcreteUnfolded ((t, dc), fields, clause) ->
       TyConcreteUnfolded ((tsubst t2 i t, dc), List.map (function
         | FieldValue (field_name, t) -> FieldValue (field_name, tsubst t2 i t)
         | FieldPermission t -> FieldPermission (tsubst t2 i t)) fields,
       tsubst t2 i clause)

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

    | TyAnd (constraints, t) ->
        let constraints = List.map (fun (f, t) ->
          f, tsubst t2 i t
        ) constraints in
        TyAnd (constraints, tsubst t2 i t)

    | TyImply (constraints, t) ->
        let constraints = List.map (fun (f, t) ->
          f, tsubst t2 i t
        ) constraints in
        TyImply (constraints, tsubst t2 i t)
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
let flatten_kind = SurfaceSyntax.flatten_kind;;

let get_arity_for_kind kind =
  let _, tl = flatten_kind kind in
  List.length tl
;;

let tsubst_data_type_group (t2: typ) (i: int) (group: data_type_group): data_type_group =
  let group = List.map (function ((name, loc, def, fact, kind) as elt) ->
    match def with
    | None, _ ->
        (* It's an abstract type, it has no branches where we should perform the
         * opening. *)
        elt

    | Some (flag, branches, clause), variance ->
        let arity = get_arity_for_kind kind in

        (* We need to add [arity] because one has to move up through the type
         * parameters to reach the typed defined at [i]. *)
        let index = i + arity in

        (* Replace each TyBound with the corresponding TyOpen, for all branches. *)
        let branches = List.map (tsubst_data_type_def_branch t2 index) branches in

        (* Do the same for the clause *)
        let clause = Option.map (tsubst t2 index) clause in
        
        let def = Some (flag, branches, clause), variance in
        name, loc, def, fact, kind
  ) group in
  group
;;

(* Substitute [t2] for [p] in [t1]. We allow [t2] to have free variables. *)
let tpsubst env (t2: typ) (p: var) (t1: typ) =
  let lift1 = lift 1 in
  let rec tsubst t2 t1 =
    match t1 with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic
    | TyBound _ ->
        t1

    | TyOpen p' ->
        if same env p p' then
          t2
        else
          t1

    | TyForall (binder, t) ->
        TyForall (binder, tsubst (lift1 t2) t)

    | TyExists (binder, t) ->
        TyExists (binder, tsubst (lift1 t2) t)

    | TyApp (t, t') ->
        TyApp (tsubst t2 t, List.map (tsubst t2) t')

    | TyTuple ts ->
        TyTuple (List.map (tsubst t2) ts)

    | TyConcreteUnfolded ((t, dc), fields, clause) ->
       TyConcreteUnfolded ((tsubst t2 t, dc), List.map (function
         | FieldValue (field_name, t) -> FieldValue (field_name, tsubst t2 t)
         | FieldPermission t -> FieldPermission (tsubst t2 t)) fields, tsubst t2 clause)

    | TySingleton t ->
        TySingleton (tsubst t2 t)

    | TyArrow (t, t') ->
        TyArrow (tsubst t2 t, tsubst t2 t')

    | TyAnchoredPermission (p, q) ->
        TyAnchoredPermission (tsubst t2 p, tsubst t2 q)

    | TyEmpty ->
        t1

    | TyStar (p, q) ->
        TyStar (tsubst t2 p, tsubst t2 q)

    | TyBar (t, p) ->
        TyBar (tsubst t2 t, tsubst t2 p)

    | TyAnd (constraints, t) ->
        let constraints = List.map (fun (f, t) -> f, tsubst t2 t) constraints in
        TyAnd (constraints, tsubst t2 t)

    | TyImply (constraints, t) ->
        let constraints = List.map (fun (f, t) -> f, tsubst t2 t) constraints in
        TyImply (constraints, tsubst t2 t)
  in
  tsubst t2 t1
;;

