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

(* This module implements a persistent store: in other words, it
   is a purely functional implementation of references, with an
   explicit store. *)

(* Memory locations are natural integers. A store is a pair of
   an allocation limit [n], which represents the next available
   memory location, and a map of integers to values, whose
   domain is the interval [0, n). Of course, there is no
   garbage collection within a store. *)

(* Maps over integers are implemented as little-endian Patricia
   trees. *)

module Map = Patricia.Little

type location =
    int

type 'a store = {
  limit: location;
  heap:  'a Map.t
}

(* The empty store. *)

let empty = {
  limit = 0;
  heap = Map.empty
}

(* Allocation. *)

let make x { limit; heap } =
  limit, { limit = limit + 1; heap = Map.add limit x heap }

(* Read access. *)

let get l { limit; heap } =
  assert (l < limit); (* can happen if user error *)
  try
    Map.find l heap
  with Not_found ->
    assert false (* cannot happen thanks to above check *)

(* Write access. *)

let set l x { limit; heap } =
  assert (l < limit); (* can happen if user error *)
  { limit; heap = Map.add l x heap }

(* Address comparison. *)

let eq (l1 : int) (l2 : int) =
  l1 = l2

let neq (l1 : int) (l2 : int) =
  l1 <> l2

let compare (l1 : int) (l2 : int) =
  l1 - l2

(* Folding an iterating *)

let iter f { heap; _ } =
  Map.iter (fun _k v -> f v) heap

let fold f acc { heap; _ } =
  Map.fold (fun k v acc -> f acc k v) heap acc

(* Misc *)

let valid l { limit; _ } =
  l < limit
