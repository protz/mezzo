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

(* A mode is a predicate on types (of kind [type]) and/or on permissions (of
   kind [perm]). *)

(* There are currently four modes: bottom, duplicable, exclusive, and affine.
   Their meaning is intuitively defined as follows: *)

(* The empty type, and only the empty type, has mode bottom. More precisely,
   if a type has mode bottom, then it must be semantically equivalent to the
   empty type, i.e., it must be uninhabited. *)

(* A type [t] is duplicable if and only if the permission [x @ t] is
   duplicable. A permission [p] is duplicable if and only if [p] is
   logically equivalent to the conjunction [p * p]. *)

(* A type [t] is exclusive if and only if the permission [x @ t] implies
   the exclusive ownership of the object at address [x]. It does not seem
   to make sense to speak of an exclusive permission; we adopt the
   convention that the predicate [exclusive] applies only to types. *)

(* Every type and every permission is affine. *)

(* Modes form a lattice, where bottom is the least element, duplicable
   and exclusive are incomparable, and affine is the top element. *)

(** The four modes. *)
type mode =
  | ModeBottom
  | ModeDuplicable
  | ModeExclusive
  | ModeAffine

(** The least element of the lattice. *)
val bottom: mode

(** The greatest element of the lattice. *)
val top: mode

(** Equality. *)
val equal: mode -> mode -> bool

(** A test for the top element of the lattice. *)
val is_maximal: mode -> bool

(** The lattice ordering. *)
val leq: mode -> mode -> bool

(** The lattice meet (i.e., greatest lower bound). *)
val meet: mode -> mode -> mode

(** Printing. *)
val print: mode -> string

(** Maps over modes. *)
module ModeMap : sig
  (** The usual operations. *)
  include Map.S with type key = mode
  (* [total f] tabulates the function [f] and produces a total map
     over modes, i.e., a map whose domain contains all modes. *)
  val total: (mode -> 'a) -> 'a t
  (* [complete f m] completes the map [m] by tabulating the function
     [f] at every missing entry. The result is again a map whose
     domain contains all modes. *)
  val complete: (mode -> 'a) -> 'a t -> 'a t
end

