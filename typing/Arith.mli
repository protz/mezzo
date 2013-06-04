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

(** This module provides arithmetic permissions support. *)

open TypeCore
open Derivations

(** [is_arith_op env v] returns true if the variable [v] is an arithmetic
 * operator. *)
val is_arith_op: env -> var -> bool

(** [fetch_arith env] returns the list of floating permissions in [env] which
 * are arithmetic. *)
val fetch_arith: env -> typ list

(** [check env consequence] is [implies (fetch_arith env) consequence]. *)
val check: env -> typ -> result
