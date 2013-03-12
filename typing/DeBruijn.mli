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

(** Dealing with binders. *)

open TypeCore

(** [lift i t] lifts type [t] by [i] *)
val lift: int -> typ -> typ

(** [tsubst t1 i t2] substitues [t1] for index [i] in [t2] *)
val tsubst : typ -> int -> typ -> typ

(** Same thing with a data type branch. *)
val tsubst_branch :
  typ ->
  int ->
  'a data_type_def_branch ->
  'a data_type_def_branch

(** Same thing with a data type group. *)
val tsubst_data_type_group :
  typ -> int -> data_type_group -> data_type_group

(** [tpsubst env t1 var t2] subtitutes [t1] for [var] in [t2]. [var] is the type
 * of open variables, so this actually {b closes} a binder. *)
val tpsubst :
  env ->
  typ -> var -> typ -> typ

val get_arity_for_kind : SurfaceSyntax.kind -> int
