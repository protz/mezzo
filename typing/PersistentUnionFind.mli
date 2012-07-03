(** A persistent version of the classic union-find algorithm. *)

(* A point. *)

type point

(* A state of the algorithm represents an equivalence relation over
   points, and a mapping of equivalence classes to descriptors of type
   ['a]. *)

type 'a state

(* [init()] produces a fresh empty state. *)

val init: unit -> 'a state

(* [create desc state] extends [state] with a new isolated point with
   descriptor [desc], producing a new state. *)

val create: 'a -> 'a state -> point * 'a state

(* [same x y state] determines whether the points [x] and [y] are
   equivalent in the state [state]. *)

val same: point -> point -> 'a state -> bool

(* [union x y state] produces a new state, which represents the least
   equivalence relation that contains [state] and makes [x] and [y]
   equivalent. The descriptor associated with [x] and [y] in the new
   state is the one associated with [y] in [state]. *)

val union: point -> point -> 'a state -> 'a state

(* [find x state] returns the descriptor associated with [x]'s
   equivalence class in the state [state]. *)

val find: point -> 'a state -> 'a

(* [update f x state] updates the descriptor associated with [x]'s equivalence
   class. The new descriptor is obtained by applying the function [f] to the
   previous descriptor. *)

val update: ('a -> 'a) -> point -> 'a state -> 'a state

(* [union_computed f x y state] first makes [x] and [y] equivalent, just like
   [union]; then, only if [x] and [y] were not already equivalent, it assigns
   a new descriptor to [x] and [y], which is computed by applying [f] to the
   descriptors previously associated with [x] and [y]. *)

val union_computed: ('a -> 'a -> 'a) -> point -> point -> 'a state -> 'a state

(* [iter f state] calls [f] with each descriptor present in the union-find. *)
val iter: ('a -> unit) -> 'a state -> unit


(* [fold f acc state] folds over all the descriptors in the union-find. *)
val fold: ('acc -> point -> 'a -> 'acc) -> 'acc -> 'a state -> 'acc

val compare: point -> point -> int

val repr: point -> 'a state -> point

val valid: point -> 'a state -> bool
