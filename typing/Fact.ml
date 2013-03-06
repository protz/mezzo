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
   definition is encoded as an integer. Referring to these variables as
   ``parameters'' helps avoid confusion with the use of the word ``variable''
   by the module [Fix]. *)

type parameter =
    int

module ParameterMap =
  Map.Make(struct
    type t = parameter
    let compare = Pervasives.compare
  end)

(* ---------------------------------------------------------------------------- *)

(* The lattice of facts. *)

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

  and so on, for every mode. For these two reasons, I define a fact to
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
   The type [t] is not explicitly represented. *)

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

(* The true hypothesis. *)

let trivial : hypothesis =
  HConjunction ParameterMap.empty

(* Conjunction of hypotheses. *)

let binary_conjunction (h1 : hypothesis) (h2 : hypothesis) : hypothesis =
  match h1, h2 with
  | HFalse, _
  | _, HFalse ->
      HFalse
  | HConjunction hs1, HConjunction hs2 ->
      (* Pointwise union of the maps, with mode *intersection* on the
	 common elements. *)
      HConjunction (ParameterMap.merge (fun _ om1 om2 ->
	match om1, om2 with
	| Some m1, Some m2 ->
	    Some (Mode.meet m1 m2)
	| Some m, None
	| None, Some m ->
	    Some m
	| None, None ->
	    assert false
      ) hs1 hs2)

let conjunction f xs =
  List.fold_left (fun accu x ->
    binary_conjunction accu (f x)
  ) trivial xs

(* The constant mode [m] is can be viewed as a fact: every mode [m']
   that is equal to or above [m] is mapped to [true], the empty conjunction,
   and every mode [m'] that does not satisfy this is mapped to [false]. *)

let constant (m : mode) : fact =
  ModeMap.total (fun m' ->
    if Mode.leq m m' then trivial else HFalse
  )

(* The bottom fact. *)

let bottom =
  constant Mode.bottom

(* A utility function for constructing a fact whose conclusion is
   a mode [m]. *)

let implication (m : mode) (h : hypothesis) : fact =
  ModeMap.total (function m' ->
    if Mode.is_maximal m' then
      trivial
    else if Mode.leq m m' then
      h
    else
      HFalse
  )

let duplicable =
  implication ModeDuplicable

(* A utility function for extending a fact with the statement
   ``without any hypotheses, this type is exclusive''. *)

let allow_exclusive (f : fact) : fact =
  ModeMap.add ModeExclusive trivial f

(* A utility function for removing the possibility that ``this
   type is exclusive''. *)

let disallow_exclusive (f : fact) : fact =
  ModeMap.add ModeExclusive HFalse f

(* Join in the lattice of facts. *)

let join fact1 fact2 =
  ModeMap.merge (fun _ oh1 oh2 ->
    match oh1, oh2 with
    | Some h1, Some h2 ->
	Some (binary_conjunction h1 h2)
    | _, _ ->
	(* These ModeMaps should be total. *)
	assert false
  ) fact1 fact2

let join_many f xs =
  List.fold_left (fun accu x ->
    join accu (f x)
  ) bottom xs

(* A fact for a parameter [p] is a conjunction of implications of
   the form [m p => m], where [m] ranges over every mode. *)

let parameter p =
  ModeMap.total (fun m ->
    HConjunction (ParameterMap.singleton p m)
  )

(* Fact equality. *)

let canonicalize (hs : hypotheses) : hypotheses =
  (* Filter out trivial hypotheses of the form [affine a]. *)
  ParameterMap.filter (fun _ m ->
    not (Mode.is_maximal m)
  ) hs

let equal fact1 fact2 =
  ModeMap.equal (fun hyp1 hyp2 ->
    match hyp1, hyp2 with
    | HFalse, HFalse ->
	true
    | HConjunction hs1, HConjunction hs2 ->
	(* Account for the fact that the maps [hs1] and [hs2] may have
	   different domains (though they logically have the same domain)
	   because trivial hypotheses may be omitted. *)
	ParameterMap.equal Mode.equal (canonicalize hs1) (canonicalize hs2)
    | HFalse, HConjunction _
    | HConjunction _, HFalse ->
	false
  ) fact1 fact2

let leq fact1 fact2 =
  ModeMap.equal (fun hyp1 hyp2 ->
    match hyp1, hyp2 with
    | _, HFalse ->
        true
    | HConjunction hs1, HConjunction hs2 ->
	(* Account for the fact that the maps [hs1] and [hs2] may have
	   different domains (though they logically have the same domain)
	   because trivial hypotheses may be omitted. *)
        (* Note that [hs2] and [hs1] are reversed, due to contravariance.
	   If [hs1] requires a parameter to have a certain mode [m1], then
	   it is fine if [hs2] requires this parameter to have a stronger
	   mode [m2]. *)
	ParameterMap.equal Mode.leq (canonicalize hs2) (canonicalize hs1)
    | HFalse, HConjunction _ ->
        false
  ) fact1 fact2

let is_trivial (hs : hypotheses) =
  let hs = canonicalize hs in
  ParameterMap.is_empty hs

(* Recognition of maximal facts -- not performed. *)

let is_maximal _ =
  (* Conservative approximation, permitted by [Fix]. *)
  false

(* [compose fact facts] composes a fact of arity [n] -- i.e. a fact
   that makes sense in the presence of [n] parameters -- with [n]
   facts about the actual parameters. If these facts have arity [k],
   then the final fact has arity [k] as well. *)

let compose fact facts =
  ModeMap.map (function
  | HFalse ->
      HFalse
  | HConjunction hs ->
      (* We are looking at a conjunction of requirements of the
	 form [m i], where [i] is one of the [n] parameters.
	 For each such requirement, we look up the [i]-th element
	 of the list [facts], and specialize it on [m], so as obtain
	 the conditions that bear on our parameters. Then, we
	 combine all of these requirements via a conjunction. *)
      ParameterMap.fold (fun i m accu ->
	binary_conjunction
	  (ModeMap.find m (List.nth facts i))
	  accu
      ) hs trivial
  ) fact

