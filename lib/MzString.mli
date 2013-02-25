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

(** Various string utilities. *)

(** Make all your pretty-printers work with buffers and use this to get a
    [Printf.sprintf] *)
val bsprintf: ('a, Buffer.t, unit, string) format4 -> 'a

(** Make all your pretty-printers work with buffers, use them with [%a] and use
    this to get a [Printf.fprintf] *)
val bfprintf : ?new_line:unit -> out_channel -> ('a, Buffer.t, unit, unit) format4 -> 'a

(** Make all your pretty-printers work with buffers, use them with [%a] and use
    this to get a [Printf.printf] *)
val bprintf : ('a, Buffer.t, unit, unit) format4 -> 'a

(** Make all your pretty-printers work with buffers, use them with [%a] and use
    this to get a [Printf.eprintf] *)
val beprintf : ('a, Buffer.t, unit, unit) format4 -> 'a

(** In case you need to ignore some stuff. *)
val biprintf : ('a, Buffer.t, unit) format -> 'a

(** [replace s1 s2 s] replaces all occurrences of [s1] with [s2] in [s]. *)
val replace: string -> string -> string -> string

(** [split s c] will split string [s] on character [c] *)
val split: string -> char -> string list

(** [substring s i j] will return all characters from string [s] comprised
 * between indices [i] (included) and [j] (excluded). *)
val substring: string -> int -> int -> string
