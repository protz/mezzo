(* A persistent version of the classic union-find algorithm. *)

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

