(* There are several flavors of algebraic data type definitions. *)

(* At the moment, there are only two flavors: a data type can be
   immutable (which implies that it is duplicable) or mutable
   (which implies that is exclusive). *)

type flavor =
  | Immutable
  | Mutable

(* Equality. *)

let equal : flavor -> flavor -> bool =
  (=)

(* Display. *)

let print = function
  | Immutable ->
      ""
  | Mutable ->
      "mutable "

(* A flavor implies a mode. *)

open Mode

let flavor2mode = function
  | Mutable ->
      ModeExclusive
  | Immutable ->
      ModeDuplicable

(* An adopter must be exclusive. *)

let can_adopt flavor =
  Mode.leq (flavor2mode flavor) ModeExclusive

(* Writing requires a mutable type. *)

let can_be_written = function
  | Mutable ->
      true
  | Immutable ->
      false

(* The [mutable] keyword may appear either in front of the algebraic
   data type definition, in which case it concerns all branches, or
   in front of a branch, in which case it concerns this branch only.
   We do not allow it to appear twice. The following helper function
   combines the two annotations. *)

let join flavor1 flavor2 fail =
  match flavor1, flavor2 with
  | Mutable, Mutable ->
      fail()
  | Mutable, Immutable
  | Immutable, Mutable ->
      Mutable
  | Immutable, Immutable ->
      Immutable

