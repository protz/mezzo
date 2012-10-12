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

(** This functor creates a fresh abstract type of names.
   It is typically invoked once for each namespace. *)

module Make (U : sig end) : sig

  (* An abstract type of names. *)

  type name

  (* Names stand for strings: names and string are inter-convertible. *)

  val register: string -> name
  val print: name -> string

  (* Names can be efficiently compared. *)

  val equal: name -> name -> bool

  (* We have efficient maps over names. *)

  module Map : GMap.S with type key = name

end

