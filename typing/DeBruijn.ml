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

open Kind
open TypeCore

(** This module provides various substitution functions. *)

(* ---------------------------------------------------------------------------- *)

(* Counting binders. *)

class map_counting = object
  (* The environment [i] has type [int]. *)
  inherit [int] map
  (* The environment [i] keeps track of how many binders have been
     entered. It is incremented at each binder. *)
  method extend i (_ : kind) =
    i + 1
end

(* ---------------------------------------------------------------------------- *)

(* Lifting. *)

class lift (k : int) = object
  inherit map_counting
  (* A local variable (one that is less than [i]) is unaffected;
     a free variable is lifted up by [k]. *)
  method tybound i j =
    if j < i then
      TyBound j
    else
      TyBound (j + k)
end

let lift (k : int) (ty : typ) : typ =
  if k = 0 then
    ty
  else
    (new lift k) # visit 0 ty

(* ---------------------------------------------------------------------------- *)

(* Substitute [t2] for [i] in [t1]. This function is easy because [t2] is
 * expected not to have any free [TyBound]s: they've all been converted to
 * [TyOpen]s. Therefore, [t2] will *not* be lifted when substituted for [i] in
 * [t1]. *)

class tsubst (t2 : typ) = object
  (* The environment [i] is the variable that we are looking for. *)
  inherit map_counting
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

let tsubst_branch (t2 : typ) (i : int) (branch : branch) =
  (new tsubst t2) # branch i branch

let tsubst_data_type_group (t2: typ) (i: int) (group: data_type_group): data_type_group =
  (new tsubst t2) # data_type_group i group

(* -------------------------------------------------------------------------- *)

(* When opening (descending under) a binder, the bound variable must be
   replaced with a (rigid or flexible) named variable. *)

let bind_in_type
    (bind: env -> type_binding -> env * var)
    (env: env)
    (binding: type_binding)
    (typ: typ)
  : env * typ * var
  =
  let env, var = bind env binding in
  let typ = tsubst (TyOpen var) 0 typ in
  env, typ, var

let bind_rigid_in_type =
  bind_in_type bind_rigid

let bind_flexible_in_type =
  bind_in_type bind_flexible

