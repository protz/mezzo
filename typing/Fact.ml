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

(* A fact is a logical statement about the mode of a type [t] that has free
   variables, or in other words, about the mode of a parameterized type [t]. *)

type property = fact

and fact =
  hypothesis ModeMap.t

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

(* Disjunction of hypotheses. Defined only when the left-hand fact has
   arity zero, i.e., it has no parameters (in other words, it is a
   constant fact). In that case, [HConjunction] is synonymous with
   [HTrue], and the definition is simple. *)

let binary_disjunction (h1 : hypothesis) (h2 : hypothesis) : hypothesis =
  match h1, h2 with
  | HFalse, h
  | h, HFalse ->
      h
  | HConjunction hs1, HConjunction _ ->
      assert (ParameterMap.cardinal hs1 = 0);
      (* [hs1] is an empty empty conjunction, i.e. it is true.
	 The result is true as well. *)
      h1

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

(* Meet in the lattice of facts. Which is not a lattice, actually,
   since meets exist only at arity zero. *)

let meet fact1 fact2 =
  ModeMap.merge (fun _ oh1 oh2 ->
    match oh1, oh2 with
    | Some h1, Some h2 ->
        Some (binary_disjunction h1 h2)
    | _, _ ->
	(* These ModeMaps should be total. *)
	assert false
  ) fact1 fact2

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

let complete fact =
  (* This code is not quite correct. In principle, if we have
     an entry at mode [m], and no entry at mode [m'], which is
     greater than [m] and not [top], then we should copy the
     entry from to [m] to [m'], so as to guarantee monotonicity
     of the resulting fact. We are in a special case where this
     situation cannot occur, because our lattice only has 4 points
     and the user cannot manually write an implication whose head
     involves the bottom mode. *)
  ModeMap.complete (fun m ->
    if Mode.is_maximal m then
      (* Every type admits the maximal mode. *)
      trivial
    else
      (* Otherwise, a missing implication is translated to an
	 implication whose hypothesis is unsatisfiable. *)
      HFalse
  ) fact

open MzPprint

let print (param : parameter -> document) (head : document) fact =
  (* TEMPORARY if the fact is "affine", then nothing is printed --
     maybe we should something about that *)
  (* Decide which implications must be printed. *)
  let implications =
    ModeMap.fold (fun m hyp accu ->
      if Mode.is_maximal m then
	(* Omit an implication whose conclusion is trivial. *)
	accu
      else
	match hyp with
	| HFalse ->
	    (* Omit an implication whose hypothesis is false. *)
	    accu
	| HConjunction hs ->
	    (hs, m) :: accu
    ) fact []
  in
  (* Print each implication. *)
  separate_map hardline (fun (hs, m) ->
    let hs = canonicalize hs in
    concat_map (fun (i, m) ->
      string (Mode.print m) ^/^ (param i) ^/^ dblarrow
    ) (ParameterMap.bindings hs) ^^
    string (Mode.print m) ^/^ head
  ) implications

let internal_print =
  print PPrintOCaml.int empty

