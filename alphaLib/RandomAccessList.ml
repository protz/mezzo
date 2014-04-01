(* This is an implementation of skew binary random access lists,
   after Okasaki's book (9.3.1). *)

(* We use complete binary trees with an element in every leaf and node. The
   weight (size) of such a tree is of the form 2^n - 1. The elements are
   stored in pre-order, that is, the head of the list is stored at the root of
   the tree. We do not store weight information at every node; we will
   maintain weight information only at the root. *)

type 'a tree =
  Leaf of 'a
| Node of 'a * 'a tree * 'a tree

module Tree = struct

(* [lookup w i t] looks up the [i]-th element of the tree [t], whose weight is
   [w]. We require [i < w]. The cost of this operation is O(log w). *)

let rec lookup w i t =
  match i, t with
  | 0, Leaf x
  | 0, Node (x, _, _) ->
      x
  | _, Node (_, l, r) ->
      let i = i - 1 in
      (* [w] is odd, so [(w - 1) / 2] is just [w / 2]. *)
      let w = w / 2 in
      if i < w then
        lookup w i l
      else
        lookup w (i - w) r
  | _, Leaf _ ->
      (* The index is out of range. *)
      assert false

(* [foldl] iterates over the elements of a tree, in pre-order. *)

let rec foldl f t accu =
  match t with
  | Leaf x ->
      f x accu
  | Node (x, l, r) ->
      let accu = f x accu in
      let accu = foldl f l accu in
      let accu = foldl f r accu in
      accu

(* [foldr] iterates over the elements of a tree, in post-order. *)

let rec foldr f t accu =
  match t with
  | Leaf x ->
      f x accu
  | Node (x, l, r) ->
      let accu = foldr f r accu in
      let accu = foldr f l accu in
      let accu = f x accu in
      accu

end

(* A random access list is a list of complete trees. This can be
   interpreted as the representation of a number in skew binary
   form, where the digits are 0, 1, and 2, the weight of a digit
   of rank i is 2^{i+1} - 1, and only the lowest non-zero digit may
   be 2. The representation is sparse: only non-zero digits
   are represented, so we have constant-time access to the lowest
   non-zero digit. A digit is represented by its weight, or rather,
   by a tree of appropriate weight. If the lowest non-zero digit
   is 2, then we represent this digit by storing two trees of
   identical weight at the head of the list. *)

type 'a t =
  Nil
| Cons of int (* weight *) * 'a tree * 'a t

(* The empty list. *)

let empty =
  Nil

(* Whether a list is empty can be determined in constant time. *)

let is_empty = function
  | Nil ->
      true
  | Cons _ ->
      false

(* Insertion corresponds to incrementing a number. Its cost is O(1). *)

let cons x = function
  | Cons (w1, t1, Cons (w2, t2, ts)) when w1 = w2 ->
      (* The lowest non-zero digit is 2. Thus, the next digit must be 0 or
         1, and it suffices to increment it, resetting the previous digit
         from 2 to 0. In either case, this is done by creating a tree of
         weight 1 + w1 + w2 and inserting it in front of the list [ts]. *)
      Cons (1 + 2 * w1, Node (x, t1, t2), ts)
  | ts ->
      (* The lowest non-zero digit is not 2. Thus, every digit is 0 or 1.
         We increment the least significant digit, and are done. *)
      Cons (1, Leaf x, ts)

(* [lookup i ts] looks up the [i]-th element of the list [ts]. The cost
   of this operation is O(log w), where [w] is the length of the list.
   It is also O(i). This operation requires [0 <= i < w]. *)

let rec lookup i = function
  | Nil ->
      assert false
  | Cons (w, t, ts) ->
      if i < w then
        Tree.lookup w i t
      else
        lookup (i - w) ts

let apply ts i =
  lookup i ts

(* [foldl] iterates over the elements of a list, in pre-order. *)

let rec foldl f ts accu =
  match ts with
  | Nil ->
      accu
  | Cons (_, t, ts) ->
      let accu = Tree.foldl f t accu in
      let accu = foldl f ts accu in
      accu

(* [foldr] iterates over the elements of a list, in post-order. *)

let rec foldr f ts accu =
  match ts with
  | Nil ->
      accu
  | Cons (_, t, ts) ->
      let accu = foldr f ts accu in
      let accu = Tree.foldr f t accu in
      accu

(* [elements] converts a random access list to an ordinary list. *)

let elements ts =
  foldr (fun x xs -> x :: xs) ts []

