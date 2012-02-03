(*****************************************************************************)
(*  ChaML, a type-checker that uses constraints and a kernel language        *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
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

(** This module provides error reporting functions for ChaML. Any module can use
    it. *)

(** Enable debugging information. *)
val enable_debug : unit -> unit

(** Report some debugging information. Use it like [Printf.printf] *)
val debug : ('a, Buffer.t, unit, unit) format4 -> 'a

(** Report a fatal error. For now, this raises an exception, but it might do
    better in the future. Use it like [Printf.printf]. *)
val error : ('a, Buffer.t, unit, 'b) format4 -> 'a

(** Assert something, otherwise display an error message and fail *)
val affirm: bool -> ('a, out_channel, unit, unit) format4 -> 'a

(** Report some debugging information. Use it like [print_string] *)
val debug_simple : string -> unit

(** Increment the debug indentation *)
val dinc : unit -> unit

(** Decrement the debug indentation *)
val ddec : unit -> unit
