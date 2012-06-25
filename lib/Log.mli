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

(** Enable debugging information. You should provide a debugging level. The
    higher the level, the more verbose the information. Currently, verbosity
    levels range from 0 (no debug messages) to 4 (all debug messages). *)
val enable_debug : int -> unit

(** Report some debugging information. Use it like [Printf.printf] *)
val debug: ?level:int -> ('a, Buffer.t, unit, unit) format4 -> 'a

(** A warning is a message that always appears, even when debug is disabled. *)
val warn: ('a, Buffer.t, unit, unit) format4 -> 'a

(** Report a fatal error. For now, this raises an exception, but it might do
    better in the future. Use it like [Printf.printf]. *)
val error: ('a, Buffer.t, unit, 'b) format4 -> 'a

(** Assert something, otherwise display an error message and fail *)
val check: bool -> ('a, out_channel, unit, unit) format4 -> 'a
