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

class lift (k : int) = object
  (* The environment [i] has type [int]. *)
  inherit [int] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method extend i (_ : type_binding) =
    i + 1
  (* A local variable (one that is less than [i]) is unaffected;
     a free variable is lifted up by [k]. *)
  method tybound i j =
    if j < i then
      TyBound j
    else
      TyBound (j + k)
end

let lift (k : int) (ty : typ) : typ =
  (new lift k) # visit 0 ty

(* Substitute [t2] for [i] in [t1]. This function is easy because [t2] is
 * expected not to have any free [TyBound]s: they've all been converted to
 * [TyOpen]s. Therefore, [t2] will *not* be lifted when substituted for [i] in
 * [t1]. *)
let rec tsubst (t2: typ) (i: int) (t1: typ) =
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
	  (* fpottier: this definition is surprising. The standard notion
	     of substitution on de Bruijn indices would be [TyBound j] if
	     [j < i] and [TyBound (j - 1)] if [j > i], because the index
	     [i] disappears in the substitution and the indices above it
	     are decremented. I tried adding the assertion [assert (j < i)],
	     which would explain why this code works, but it fails. This is
	     due apparently to the auxiliary function [subst_type], nested
	     within [Expressions.bind_evars], which opens a sequence of
	     bindings by opening the *innermost* binding first. This is
	     counter-intuitive. Maybe we could:
	     1. fix [Expressions.bind_evars] so that it opens the outermost
	        binding first; (just open the bindings one by one;)
	     2. add [assert (j < i)] and makes sure that it succeeds;
	     3. potentially allow [TyBound (if j < i then j else j-1)],
	        which is more general. *)

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

    | TyConcreteUnfolded branch ->
       TyConcreteUnfolded (tsubst_resolved_branch t2 i branch)

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

    | TyAnd ((m, t), u) ->
        TyAnd ((m, tsubst t2 i t), tsubst t2 i u)

    | TyImply ((m, t), u) ->
        TyImply ((m, tsubst t2 i t), tsubst t2 i u)

and tsubst_resolved_branch t2 i branch = {
  branch_flavor = branch.branch_flavor;
  branch_datacon = tsubst_resolved_datacon t2 i branch.branch_datacon;
  branch_fields = List.map (tsubst_field t2 i) branch.branch_fields;
  branch_adopts = tsubst t2 i branch.branch_adopts;
}

and tsubst_resolved_datacon t2 i (t, dc) =
  (tsubst t2 i t, dc)

and tsubst_field t2 i = function
  | FieldValue (name, typ) ->
      FieldValue (name, tsubst t2 i typ)
  | FieldPermission typ ->
      FieldPermission (tsubst t2 i typ)
;;

let tsubst_unresolved_branch t2 i branch = {
  branch_flavor = branch.branch_flavor;
  branch_datacon = branch.branch_datacon;
  branch_fields = List.map (tsubst_field t2 i) branch.branch_fields;
  branch_adopts = tsubst t2 i branch.branch_adopts;
}

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

    | Some branches, variance ->
        let arity = get_arity_for_kind kind in

        (* We need to add [arity] because one has to move up through the type
         * parameters to reach the typed defined at [i]. *)
        let index = i + arity in

        (* Replace each TyBound with the corresponding TyOpen, for all branches. *)
        let branches = List.map (tsubst_unresolved_branch t2 index) branches in

        let def = Some branches, variance in
        name, loc, def, fact, kind
  ) group in
  group
;;

(* Substitute [t2] for [p] in [t1]. We allow [t2] to have free variables. *)
let tpsubst env (t2: typ) (p: var) (t1: typ) =
  let rec tpsubst t2 t1 =
    let t1 = modulo_flex env t1 in
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
        TyForall (binder, tpsubst (lift 1 t2) t)

    | TyExists (binder, t) ->
        TyExists (binder, tpsubst (lift 1 t2) t)

    | TyApp (t, t') ->
        TyApp (tpsubst t2 t, List.map (tpsubst t2) t')

    | TyTuple ts ->
        TyTuple (List.map (tpsubst t2) ts)

    | TyConcreteUnfolded branch ->
       TyConcreteUnfolded (tpsubst_branch t2 branch)

    | TySingleton t ->
        TySingleton (tpsubst t2 t)

    | TyArrow (t, t') ->
        TyArrow (tpsubst t2 t, tpsubst t2 t')

    | TyAnchoredPermission (p, q) ->
        TyAnchoredPermission (tpsubst t2 p, tpsubst t2 q)

    | TyEmpty ->
        t1

    | TyStar (p, q) ->
        TyStar (tpsubst t2 p, tpsubst t2 q)

    | TyBar (t, p) ->
        TyBar (tpsubst t2 t, tpsubst t2 p)

    | TyAnd ((m, t), u) ->
        TyAnd ((m, tpsubst t2 t), tpsubst t2 u)

    | TyImply ((m, t), u) ->
        TyImply ((m, tpsubst t2 t), tpsubst t2 u)

  and tpsubst_branch t2 branch = {
    branch_flavor = branch.branch_flavor;
    branch_datacon = tpsubst_resolved_datacon t2 branch.branch_datacon;
    branch_fields = List.map (tpsubst_field t2) branch.branch_fields;
    branch_adopts = tpsubst t2 branch.branch_adopts;
  }

  and tpsubst_field t2 = function
    | FieldValue (field_name, t) -> FieldValue (field_name, tpsubst t2 t)
    | FieldPermission t -> FieldPermission (tpsubst t2 t)

  and tpsubst_resolved_datacon t2 (t, dc) =
    tpsubst t2 t, dc

  in
  tpsubst t2 t1
;;

