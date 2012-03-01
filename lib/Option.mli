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

(** No "J" prefix for this module since OCaml's standard library does not have
    an [Option] module. *)

(** [map] [f] [opt] maps [None] to [None] and [Some a] to [Some (f a)] *)
val map : ('a -> 'b) -> 'a option -> 'b option

(** [map_none] [n] [opt] maps [None] to [n] and [Some m] to [m]. *)
val map_none : 'a -> 'a option -> 'a

(** Since [unit option] and [bool] are isomorphic, this function implements the
    morphism from [unit option] to [bool]. [None] maps to [false] and [Some ()]
    to true. *)
val unit_bool : unit option -> bool

(** When you're sure you have [Some] *)
val extract: 'a option -> 'a

(** The name speaks for itself *)
val iter: ('a -> unit) -> 'a option -> unit

(** Maps [None] to [None] and [Some x] to [f x]. *)
val bind: 'a option -> ('a -> 'b option) -> 'b option
