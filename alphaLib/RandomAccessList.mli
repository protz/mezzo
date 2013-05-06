(** A random access list is a data structure that implements a sequence
    of elements and supports efficient [cons] and [lookup] operations. *)

(* More operations, including, [head], [tail], and [update], could be
   efficiently implemented if desired. *)

(** ['a t] is the type of lists whose elements have type ['a]. *)
type 'a t

(** The empty list. *)
val empty: 'a t

(** Whether a list is empty can be determined in constant time. *)
val is_empty: 'a t -> bool

(** [cons x xs] is the list obtained by inserting [x] in front of the
    list [xs]. The cost of this operation is O(1). *)
val cons: 'a -> 'a t -> 'a t

(** [lookup i xs] looks up the [i]-th element of the list [xs]. The cost
    of this operation is O(log w), where [w] is the length of the list.
    It is also O(i). This operation requires [0 <= i < w]. *)
val lookup: int -> 'a t -> 'a
val apply : 'a t -> int -> 'a

(** [foldl] iterates over the elements of a list, in pre-order. *)
val foldl: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(** [foldr] iterates over the elements of a list, in post-order. *)
val foldr: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(** [elements] converts a random access list to an ordinary list. *)
val elements: 'a t -> 'a list

