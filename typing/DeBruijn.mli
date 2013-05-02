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
val tsubst_unresolved_branch: typ -> int -> unresolved_branch -> unresolved_branch

(** Same thing with a data type group. *)
val tsubst_data_type_group : typ -> int -> data_type_group -> data_type_group

(** [bind_rigid_in_type env binding ty] opens the binding [binding], whose scope
    is the type [ty], by replacing the bound variable with a rigid variable. It
    returns a triple of an extended environment, the new [ty], and the variable
    that was created. *)
val bind_rigid_in_type :
  env -> type_binding -> typ ->
  env * typ * var

(** [bind_rigid_in_type env binding ty] opens the binding [binding], whose scope
    is the type [ty], by replacing the bound variable with a new flexible variable. *)
val bind_flexible_in_type :
  env ->
  type_binding ->
  typ -> env * typ * var
