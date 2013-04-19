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

(** A bunch of useful functions for lists. *)

(** Same as [map2] but pass an extra parameter that represents the index *)
val map2i: (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

(** Same as [fold_right] except that the function takes the current index in the
   list. The index starts counting from the right of the list, so the first call
   will pass 0 for [i]. *)
val fold_righti: (int -> 'elt -> 'acc -> 'acc) -> 'elt list -> 'acc -> 'acc

(** Same as [fold_left] except that the function takes the current index in the
   list *)
val fold_lefti: (int -> 'acc -> 'elt -> 'acc) -> 'acc -> 'elt list -> 'acc

(** Same as [fold_left2] except that the function takes the current index in the
   list *)
val fold_left2i: (int -> 'acc -> 'b -> 'c -> 'acc) -> 'acc -> 'b list -> 'c list -> 'acc

(** Same as [fold_left2] but with three lists. *)
val fold_left3: ('acc -> 't1 -> 't2 -> 't3 -> 'acc) -> 'acc -> 't1 list -> 't2 list -> 't3 list -> 'acc

(** Same as [fold_left], but start folding on the head of the list instead of
    giving an initial element. *)
val reduce: ('a -> 'a -> 'a) -> 'a list -> 'a

(** Same as [List.iteri] but with two lists. *)
val iter2i : (int -> 'a -> 'b -> unit) -> 'a list -> 'b list -> unit

(** Same as [List.iter] but with three lists. *)
val iter3 : ('a -> 'b -> 'c -> unit) -> 'a list -> 'b list -> 'c list -> unit

(** Same as [List.combine] but for triples instead of pairs. *)
val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

(** Same as [List.split] but for triples instead of pairs. *)
val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

(** [make n f] creates [[f 1; ...; f n]]. *)
val make: int -> (int -> 'a) -> 'a list

(** Get the last element of a list. *)
val last: 'a list -> 'a

(** Map a function and then discard the result. *)
val ignore_map : ('a -> 'b) -> 'a list -> unit

(** Checking for duplicates in a list. [check_for_duplicates compare xs] returns either
    [Some (x1, x2)] where [x1] and [x2] are distinct elements of the list [xs] such
    that [compare x1 x2] is zero, or [None], if no such two elements exist. *)
val check_for_duplicates : ('a -> 'a -> int) -> 'a list -> ('a * 'a) option

(** Checking for duplicates in a list. The comparison function operates on values
    of type ['b], while the list elements have type ['a]. A projection function
    maps ['a] to ['b]. If a duplicate element is found, the exit function is
    invoked. *)
val exit_if_duplicates: ('b -> 'b -> int) -> ('a -> 'b) -> 'a list -> ('b -> unit) -> unit

(** Find the biggest element in a list *)
val max: int list -> int

(** Turns [[Some a; None; ...]] into [[a; ...]] *)
val filter_some: 'a option list -> 'a list

(** Just like [List.nth] except it returns an [Option] type. *)
val nth_opt: 'a list -> int -> 'a option

(** Map and discard some elements at the same time. *)
val map_some: ('a -> 'b option) -> 'a list -> 'b list

(** Find the index of the first element in a list that satisfies a predicate. *)
val index: ('a -> bool) -> 'a list -> int

(** If [f] may convert an 'a into a 'b, then [take f l] returns the first
   convertible element in the list, along with the remaining elements in the
   list. *)
val take: ('a -> 'b option) -> 'a list -> ('a list * ('a * 'b)) option
val take_bool: ('a -> bool) -> 'a list -> ('a list * 'a) option

val find_opt: ('a -> 'b option) -> 'a list -> 'b option

val map_flatten: ('a -> 'b list) -> 'a list -> 'b list

val cut: int -> 'a list -> 'a list

(** Equality of lists, up to equality of elements. *)
val equal: ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

(** A CPS version of [List.map]. *)
val cps_map:
  ('a -> ('b -> 'c) -> 'c) ->
  'a list -> ('b list -> 'c) -> 'c

(** A sharing-preserving version of [List.map]. *)
val map: ('a -> 'a) -> 'a list -> 'a list
