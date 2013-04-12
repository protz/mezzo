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

(** This module implements a persistent store: in other words, it
   is a purely functional implementation of references, with an
   explicit store. *)

type location

type 'a store

(* The empty store. *)

val empty: 'a store

(* Allocation. *)

val make: 'a -> 'a store -> location * 'a store

(* Read access. *)

val get: location -> 'a store -> 'a

(* Write access. *)

val set: location -> 'a -> 'a store -> 'a store

(* Iterating on all locations. *)

val iter: ('a -> unit) -> 'a store -> unit

(* Folding *)

val fold: ('acc -> location -> 'a -> 'acc) -> 'acc -> 'a store -> 'acc

(* Address comparison. *)

val eq: location -> location -> bool
val neq: location -> location -> bool
val compare: location -> location -> int

(* Additional tests. *)

val valid: location -> 'a store -> bool
