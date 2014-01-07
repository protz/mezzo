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

(** This module implements the merge operation. *)

open TypeCore

type t = (env * var) * (var list * var list)

(** When the control-flow diverges, one needs to merge the environments, that
 * is, compute a set of permissions that subsumes the two environments. In order
 * to run, the [merge_envs] function takes:
 * - a [top] environment which represents the original environment before the
 *   control-flow started to diverge,
 * - an optional type annotation which may contain a list of expected
 *   permissions to be available after this merge operation
 * - a pair of the left environment, and the variable that represents the return
 *   value computed in the left environment
 * - the same thing for the right environment.
 *
 * It returns a merged environment along with a variable that points to the
 * combined return value of the merged environment.
 *
 * Consider for example "if True then x else y"; the combined return value of
 * the two environments will try to reconcile the permissions available for "x"
 * and "y". *)
val merge_envs: env -> ?annot:typ -> env * var -> env * var -> t
