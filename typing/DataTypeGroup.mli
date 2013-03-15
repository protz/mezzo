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

(** Everything you need to properly deal with data type groups.
 *
 * This module takes care of opening a group of definitions in a file, and
 * running the various analyses required ({!Variance}, {!FactInference}). *)

open TypeCore
open Expressions

(** This function processes a {!data_type_group}, and opens the corresponding
 * binders in the {!toplevel_item}s that follow. The resulting {!toplevel_item}s
 * are returned, as well as the list of {!var}s that have been bound. *)
val bind_data_type_group: env -> data_type_group -> toplevel_item list ->
      env * toplevel_item list * var list
