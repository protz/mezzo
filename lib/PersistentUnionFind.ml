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

(* A persistent version of the classic union-find algorithm. *)

(* The internal representation of the state of the algorithm is
   not just a persistent store, but a reference to a persistent
   store. This allows path compression to update the store in
   place, and leads to slightly more efficient code (this saves
   the need for allocating pairs) and a slightly more pleasant
   user interface ([find] does not need to return a new state). *)

open PersistentRef

(* A state of the union-find algorithm is a reference to a
   persistent store, where each memory location holds either
   [Link] -- a pointer to another location -- or [Root]. *)

type 'a content =
  | Link of location
  | Root of 'a

type 'a state =
    'a content store ref

(* Points are memory locations. *)

type point =
    location

(* [repr x state] finds the root of the equivalence class of [x]
   in the state [state]. Path compression is performed, and the
   state is updated in place; this update is not observable by
   the client. *)

let rec repr x state =
   match get x !state with
   | Root _ ->
       x
   | Link y ->
       let z = repr y state in
       if neq y z then
        (* updating the state in place is ok, because the meaning
           of this state is unchanged *)
        state := set x (get y !state) !state;
       z

(* [init()] produces a fresh empty state. *)

let init () =
  ref empty

(* [create desc state] creates a new isolated point with descriptor
   [desc], producing a new state. *)

let create desc state =
   let l, store = make (Root desc) !state in
   l, ref store

(* [same x y state] determines whether the points [x] and [y] are
   equivalent in the state [state]. *)

let same x y state =
  eq (repr x state) (repr y state)

(* [union x y state] produces a new state, which represents the least
   equivalence relation that contains [state] and makes [x] and [y]
   equivalent. The descriptor associated with [x] and [y] in the new
   state is the one associated with [y] in [state]. *)

let union x y state =
  let rx = repr x state in
  let ry = repr y state in
  if eq rx ry then
    state
  else
     (* careful: an in-place update would not be ok here! *)
     ref (set rx (Link ry) !state)

(* [find x state] returns the descriptor associated with [x]'s
   equivalence class in the state [state]. *)

let find x state =
  let store = !state in
  match get x store with
  | Root desc ->
      desc
  | Link y ->
      match get y store with
      | Root desc ->
         desc
      | Link _ ->
         let r = repr x state in
         match get r !state with
         | Root desc ->
             desc
         | Link _ ->
             assert false

(* [update f x state] updates the descriptor associated with [x]'s equivalence
   class. The new descriptor is obtained by applying the function [f] to the
   previous descriptor. *)

let update f x state =
  let rx = repr x state in
  let descx = find rx state in
  (* careful: an in-place update would not be ok here! *)
  ref (set rx (Root (f descx)) !state)

(* [union_computed f x y state] first makes [x] and [y] equivalent, just like
   [union]; then, only if [x] and [y] were not already equivalent, it assigns
   a new descriptor to [x] and [y], which is computed by applying [f] to the
   descriptors previously associated with [x] and [y]. *)

let union_computed f x y state =
  let rx = repr x state in
  let ry = repr y state in
  if eq rx ry then
    state
  else
     (* careful: an in-place update would not be ok here! *)
     let store = set rx (Link ry) !state in
     let descx = find rx state
     and descy = find ry state in
     (* careful: an in-place update would not be ok here! *)
     let store = set ry (Root (f descx descy)) store in
     ref store


let iter f state =
  iter (function Link _ -> () | Root v -> f v) !state

let fold f acc state =
  fold (fun acc k -> function
    | Link _ -> acc
    | Root v -> f acc k v) acc !state

let compare = PersistentRef.compare

let valid p state = PersistentRef.valid p !state
