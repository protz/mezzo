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

(** Provides wrappers for some bash fancy printing, mainly boxes and colors. *)

(** A set of nice colors. *)
type colors = {
  green: string;
  red: string;
  blue: string;
  yellow: string;
  orange: string;
  default: string;
  underline: string;
}

(** They have been chosen arbitrarily out of the 256-color set available. *)
val colors : colors

(** The terminal's width. *)
val twidth : int

(** The terminal's height. *)
val theight : int

(** Make a title. *)
val box : string -> string

(** Reset the cursor to the top-left corner of the screen *)
val reset : unit -> unit
