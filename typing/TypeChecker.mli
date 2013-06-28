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

(** This is the top of the pyramid: the module that actually performs
 * type-checking. *)

open TypeCore

(** [check_declaration_group env declarations items] type-checks a set of
 * top-level [declarations]; in order to do that, it will end up opening certain
 * binders, which is why it takes a list of [items] which will be correctly
 * transformed so as to refer to the variables that have been opened. It returns
 * an environment, the transformed [items], and the list of opened variables. *)
val check_declaration_group :
  env ->
  ExpressionsCore.definitions ->
  ExpressionsCore.toplevel_item list ->
  env * ExpressionsCore.toplevel_item list * var list

val check_function_call: env -> ?annot: typ -> var -> var -> env * typ
