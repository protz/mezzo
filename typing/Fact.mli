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

open Mode

(* ---------------------------------------------------------------------------- *)

(* A type variable that serves as a parameter in an algebraic data type
   definition is encoded as an integer. *)

type parameter =
    int

module ParameterMap :
  Map.S with type key = parameter

(* ---------------------------------------------------------------------------- *)

(* A fact is a logical statement about the mode of a type [t] that has free
   variables, or in other words, about the mode of a parameterized type [t]. *)

(* Example facts are:
   
    duplicable int
    exclusive (ref a)
    duplicable a => duplicable (list a)
    duplicable a => duplicable b => duplicable (map a b)

  We may wish to allow several implications to concern the same type
  constructor. This could be useful, in particular, to deal with
  arrays. The type array could be exclusive or duplicable, depending
  on one of its parameters. Thus, the following conjunction of two
  implications would form a fact about the type array:

    duplicable m => duplicable a => duplicable (array m a)
    exclusive m => exclusive (array m a)

  Multiple implications are useful also for a more technical reason.
  In the base case of parameters, it seems convenient to write:

    duplicable a => duplicable a
    exclusive a => exclusive a

  and so on, for every mode. For these two reasons, we define a fact to
  be a conjunction of implications. The conclusion of each implication
  is a mode assertion of the form [m t], where the type [t] has free
  parameters. The hypotheses are mode assertions about these parameters.
  Distinct implications have distinct modes [m] in their conclusions,
  and we maintain a monotonicity property: if one implication is
  [h1 => m1 t] and another is [h2 => m2 t], where [m1 <= m2], then
  [h1] implies [h2]. This ensures that [h2] is indeed a necessary
  condition for [m2 t] to hold. *)

type property = fact

(* A fact about a type [t] is represented as a total function from
   a mode [m] -- the mode in the conclusion -- to a hypothesis [h].
   The type [t] itself is not explicitly represented. *)

and fact =
  hypothesis ModeMap.t

(* A hypothesis is either [false] or a conjunction of mode constraints
   bearing on the parameters. This conjunction is represented as a
   total function from parameters to modes. The domain of the parameters
   is finite and depends on the type [t]. It is not explicitly specified
   here. If a parameter is not explicitly mentioned in the conjunction,
   we assume that there is a trivial hypothesis about it, i.e., it is
   assumed to be affine. This convention allows the empty conjunction
   to be represetented by an empty map, independently of the number of
   parameters in existence. *)

and hypothesis =
  | HFalse
  | HConjunction of hypotheses

and hypotheses =
    mode ParameterMap.t

(* Facts form a lattice. The join operation is performed point-wise
   (per goal mode), and for each mode, a conjunction of hypotheses
   is performed. The bottom fact is [constant Mode.bottom]. *)

(* ---------------------------------------------------------------------------- *)

(* Operations on hypotheses. *)

(** Conjunction of hypotheses. *)
val conjunction: ('a -> hypothesis) -> 'a list -> hypothesis

(* ---------------------------------------------------------------------------- *)

(* Lattice operations. *)

(** The least fact is defined as [constant Mode.bottom]. *)
val bottom: fact

(** Equality. *)
val equal: fact -> fact -> bool

(** The lattice ordering. *)
val leq: fact -> fact -> bool

(** The lattice join (i.e., least upper bound). *)
val join: fact -> fact -> fact
val join_many: ('a -> fact) -> 'a list -> fact

(** The lattice meet. Beware: this operation is defined only for facts
    of arity zero. (These facts are isomorphic to modes, and this
    operation has the same effect as [Mode.meet].) *)
val meet: fact -> fact -> fact

(** Recognition of maximal facts is not performed. This function
    is provided for the benefit of [Fix]. *)
val is_maximal: fact -> bool

(* ---------------------------------------------------------------------------- *)

(* Operations for constructing facts. *)

(** A mode [m] can be viewed as a fact: every mode [m'] that is equal
    to or above [m] is mapped to [true], the empty conjunction, and
    every mode [m'] that does not satisfy this is mapped to [false]. *)
val constant: mode -> fact

(** [implication h m] constructs a fact of the form [h => m]. (More
    precisely, in this fact, the top mode is mapped to the hypothesis
    [trivial]; every (non-top) mode greater than or equal to [m] is
    mapped to the hypothesis [h]; and every other mode is mapped to
    the hypothesis [HFalse].) *)
val implication: mode -> hypothesis -> fact

(** [duplicable] is [implication ModeDuplicable]. *)
val duplicable: hypothesis -> fact

(** A utility function for extending a fact with the statement
    ``without any hypotheses, this type is exclusive''. *)
val allow_exclusive: fact -> fact

(** A utility function for removing the possibility that ``this
    type is exclusive''. *)
val disallow_exclusive: fact -> fact

(** A fact for a parameter [p] is a conjunction of implications of
    the form [m p => m], where [m] ranges over every mode. *)
val parameter: parameter -> fact

(** [compose fact facts] composes a fact of arity [n] -- i.e. a fact
    that makes sense in the presence of [n] parameters -- with [n]
    facts about the actual parameters. If these facts have arity [k],
    then the final fact has arity [k] as well. *)
val compose: fact -> fact list -> fact

(** [complete fact] completes an incomplete fact (i.e., a mode map
    whose domain does not contain all modes) so as to obtain a valid
    fact. Use with caution. *)
val complete: fact -> fact

(* ---------------------------------------------------------------------------- *)

(* Printing. *)

open PPrint

(** [print param head fact] is a textual representation of the fact
    [fact]. The function [param] is used to map a parameter to its textual
    representation. [head] is a textual representation of the type that
    appears in the goals. *)
val print: (parameter -> document) -> document -> fact -> document

(** [internal_print fact] is a textual representation of the fact
    [fact]. Parameters are represented by their number, and there
    is no head. This is for internal use. *)
val internal_print: fact -> document

