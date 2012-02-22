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

(** A bunch of useful functions for lists. *)

(** Same as [map] but pass an extra parameter that represents the index *)
val mapi: (int -> 'a -> 'b) -> 'a list -> 'b list

(** Same as [map2] but pass an extra parameter that represents the index *)
val map2i: (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

(** Same as [fold_left] except that the function takes the current index in the
   list *)
val fold_lefti: (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

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

(** Same as [List.split] but for triples instead of pairs. *)
val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

(** [make n f] creates [[f 1; ...; f n]]. *)
val make: int -> (int -> 'a) -> 'a list

(** Get the last element of a list. *)
val last: 'a list -> 'a

(** Map a function and then discard the result. *)
val ignore_map : ('a -> 'b) -> 'a list -> unit

(** [append_rev_front l1 l2] is tail-rec and returns [(List.rev l1) :: l2]. *)
val append_rev_front : 'a list -> 'a list -> 'a list

(** Remove duplicates from a list. You can provide a hash function as well as a
    custom equality function. The constraint is that two equal elements must
    have the same hash. Use [Hashtbl.hash_func] if needed. *)
val remove_duplicates :
  ?hash_func:('a -> int) ->
  ?equal_func:('a -> 'a -> bool) -> 'a list -> 'a list

(** Find the biggest element in a list *)
val max: int list -> int

(** Turns [[Some a; None; ...]] into [[a; ...]] *)
val filter_some: 'a option list -> 'a list

(** Just like [List.nth] except it returns an [Option] type. *)
val nth_opt: 'a list -> int -> 'a option
