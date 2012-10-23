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
        TyApp (clean t1, List.map clean t2)

      (* Structural types. *)
    | TyTuple ts ->
        TyTuple (List.map clean ts)

    | TyConcreteUnfolded (datacon, fields, clause) ->
        let fields = List.map (function
          | FieldValue (f, t) ->
              FieldValue (f, clean t)
          | FieldPermission p ->
              FieldPermission (clean p)
        ) fields in
        TyConcreteUnfolded (datacon, fields, clean clause)

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
        Datacon.equal name1 name2 &&
        equal clause1 clause2 &&
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
        TyApp (lift i t1, List.map (lift i) t2)

    | TyTuple ts ->
        TyTuple (List.map (lift i) ts)

    | TyConcreteUnfolded (name, fields, clause) ->
        TyConcreteUnfolded (
          name,
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
        TyApp (tsubst t2 i t, List.map (tsubst t2 i) t')

    | TyTuple ts ->
        TyTuple (List.map (tsubst t2 i) ts)

    | TyConcreteUnfolded (name, fields, clause) ->
       TyConcreteUnfolded (name, List.map (function
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

        (* Replace each TyVar with the corresponding TyPoint, for all branches. *)
        let branches = List.map (tsubst_data_type_def_branch t2 index) branches in

        (* Do the same for the clause *)
        let clause = Option.map (tsubst t2 index) clause in
        
        let def = Some (flag, branches, clause), variance in
        name, loc, def, fact, kind
  ) group in
  group
;;