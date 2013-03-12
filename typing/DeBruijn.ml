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

(* Lifting. *)

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

(* ---------------------------------------------------------------------------- *)

(* Substitute [t2] for [i] in [t1]. This function is easy because [t2] is
 * expected not to have any free [TyBound]s: they've all been converted to
 * [TyOpen]s. Therefore, [t2] will *not* be lifted when substituted for [i] in
 * [t1]. *)

class tsubst (t2 : typ) = object
  (* The environment [i] has type [int]. It is the variable that
     we are looking for. *)
  inherit [int] map
  (* The environment [i] is incremented at each binder. *)
  method extend i (_ : type_binding) =
    i + 1
  (* The target variable [i] is replaced with [t2]. Any other
     variable is unaffected. *)
  method tybound i j =
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
end

let tsubst (t2 : typ) (i : int) (t1 : typ) =
  (new tsubst t2) # visit i t1

let tsubst_unresolved_branch (t2 : typ) (i : int) (branch : unresolved_branch) =
  (new tsubst t2) # unresolved_branch i branch

let tsubst_data_type_group (t2: typ) (i: int) (group: data_type_group): data_type_group =
  let group = List.map (function ((name, loc, def, fact, kind) as elt) ->
    match def with
    | None, _ ->
        (* It's an abstract type, it has no branches where we should perform the
         * opening. *)
        elt

    | Some branches, variance ->
        let arity = SurfaceSyntax.get_arity_for_kind kind in

        (* We need to add [arity] because one has to move up through the type
         * parameters to reach the type defined at [i]. *)
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

