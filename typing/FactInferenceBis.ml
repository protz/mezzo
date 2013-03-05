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

open TypeCore
open Types

(* ---------------------------------------------------------------------------- *)

(* The lattice of modes. *)

module Mode = struct

  (* Only an empty type (i.e. a type that is semantically equivalent to
     [TyBottom]) has mode [ModeBottom]. *)

  (* A type [t] is duplicable if and only if the permission [x @ t] is
     duplicable. A permission [p] is duplicable if and only if [p] is
     logically equivalent to the conjunction [p * p]. *)

  (* A type [t] is exclusive if and only if the permission [x @ t] implies
     the exclusive ownership of the object at address [x]. *)

  (* I don't know if we could define what it means for a permission [p] to
     be exclusive. I will assume that when we write [exclusive t], [t] has
     kind [type]. *)

  (* Every type and every permission is affine. *)  

  type mode =
    | ModeBottom
    | ModeDuplicable
    | ModeExclusive
    | ModeAffine

  type t = mode

  (* Basic operations. *)

  let equal : mode -> mode -> bool =
    (=)

  let compare : mode -> mode -> int =
    Pervasives.compare

  let bottom =
    ModeBottom

  let top =
    ModeAffine

  let is_maximal = function
    | ModeAffine ->
	true
    | _ ->
	false

  let leq m1 m2 =
    match m1, m2 with
    | ModeBottom, _
    | _, ModeAffine
    | ModeDuplicable, ModeDuplicable
    | ModeExclusive, ModeExclusive ->
	true
    | _, _ ->
	false

  let modes =
    [ ModeBottom; ModeDuplicable; ModeExclusive; ModeAffine ]

  let fold f accu =
    List.fold_left f accu modes

end

module ModeMap = struct
  
  include Map.Make(Mode)

  (* Building a total map over modes. *)

  let total (f : Mode.mode -> 'a) : 'a t =
    Mode.fold (fun accu m ->
      add m (f m) accu
    ) empty

end

open Mode

(* ---------------------------------------------------------------------------- *)

(* A type variable is encoded as an integer. We refer to these variables as
   ``parameters'' in order to avoid confusion with the use of the word
   ``variable'' by the module [Fix]. *)

module Parameter = struct

  type parameter = int

  type t = parameter

  let compare : parameter -> parameter -> int =
    Pervasives.compare

end

module ParameterMap =
  Map.Make(Parameter)

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

module Fact = struct

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

  (* Operations. *)

  (* The constant mode [m] is can be viewed as a fact: every mode [m']
     that is equal to or above [m] is mapped to [true], the empty conjunction,
     and every mode [m'] that does not satisfy this is mapped to [false]. *)

  let constant m =
    ModeMap.total (fun m' ->
      if Mode.leq m m' then
        HConjunction ParameterMap.empty
      else
	HFalse
    )

  let bottom =
    constant Mode.bottom

  (* The fact that we construct for a parameter [p] is a conjunction of
     implications of the form [m p => m]. *)

  let parameter p =
    ModeMap.total (fun m ->
      HConjunction (ParameterMap.singleton p m)
    )

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

  let is_maximal _ =
    (* Conservative approximation, permitted by [Fix]. *)
    false

end

(* ---------------------------------------------------------------------------- *)

(* This glue code adapts the type [TypeCore.fact], used in the environment, to
   our internal representation of modes, which is different. *)

(* TEMPORARY ultimately, the environment itself should be adapted *)

let adapt (f : TypeCore.fact) : mode =
  match f with
  | Exclusive ->
      ModeExclusive
  | Duplicable bitmap ->
      assert (Array.length bitmap = 0);
      ModeDuplicable
  | Affine ->
      ModeAffine
  | Fuzzy _ ->
      (* no longer used *)
      assert false

(* ---------------------------------------------------------------------------- *)

(* Inferring a fact about a type. *)

(* [VarMap] supports rigid variables only. *)

let infer (env : env) (parameters: Parameter.t VarMap.t) (assumptions: mode VarMap.t) (ty : typ) : Fact.fact =
  let ty = modulo_flex env ty in
  match ty with

  (* A type variable, represented by [TyOpen _], could be a local variable
     (e.g. introduced by a universal quantifier which we have just entered)
     or a parameter or a pre-existing variable. In the first two cases, it
     must be rigid, I think; in the last case, it could be rigid or flexible. *)

  | TyOpen v when is_rigid env v && VarMap.mem v assumptions ->

      (* [v] is present in [assumptions], so we are in the first case:
	 [v] is local. Our assumptions tell us that [v] has mode [m]. We
	 produce the fact [m], without any hypotheses on the parameters. *)
      let m : mode = VarMap.find v assumptions in
      Fact.constant m

  | TyOpen v when is_rigid env v && VarMap.mem v parameters ->

      (* [v] is present in [parameters], so we are in the second case:
	 [v] is a parameter [p]. We produce a fact of the form [m p => m],
	 for every mode [m]. This means ``for every mode [m], if the
	 parameter [p] has mode [m], then this type has mode [m].'' *)
      let p : Parameter.t = VarMap.find v parameters in
      Fact.parameter p

  | TyOpen v ->

      (* [v] is not present in [assumptions] or [parameters], so it is
	 external. We look up the environment in order to obtain a mode [m]
	 for [v], and turn it into a constant fact [m]. *)
      Fact.constant (adapt (get_fact env v))


let is_exclusive_fact = function
  | Exclusive ->
      true
  | Affine
  | Duplicable _ ->
      false
  | Fuzzy _ ->
      (* TEMPORARY get rid of this case? *)
      assert false

let rec is_exclusive (env : env) (ty : typ) : bool =
  let ty = modulo_flex env ty in
  match ty with

  | TyOpen point ->
      (* When we find a free type variable, we look it up in the environment.
	 We may have a hypothesis about it. *)
      is_exclusive_fact (get_fact env point)

  (* Comments on universal types. *)

  (* A weird type such as ([a] duplicable a => ref int) is logically equivalent
   * to (ref int), hence is exclusive. Similarly, ([a] exclusive a => ref int) is
   * exclusive. And ([a] duplicable a => exclusive a => ref int) is logically
   * equivalent to (ref int), because the type bottom is both exclusive and
   * duplicable. *)

  (* When trying to prove that [a]u is exclusive, we might wish to assume that
     a has fact bottom in the lattice of facts, or equivalently (?), we might
     wish to instantiate a with the type bottom. This is not implemented yet. *)

  (* For the moment, we assume that a is exclusive; this is sound and only very
     marginally incomplete. *)

  | TyForall ((binding, _), t') ->
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var Exclusive in
      is_exclusive env t'

  | TyExists (binding, t') ->
      (* Be conservative: assume that the quantified variable is affine. *)
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var Affine in
      is_exclusive env t'

  | TyApp (cons, _) ->
      is_exclusive_fact (get_fact env !!cons)

  | TyConcreteUnfolded (datacon, _, _) ->
      let flag, _, _ = def_for_datacon env datacon in
      begin match flag with
      | SurfaceSyntax.Exclusive ->
	  true
      | SurfaceSyntax.Duplicable ->
	  false
      end

  (* Comments about constraints. *)

  (* The existential type {a} (exclusive a /\ a) is exclusive.
     Similarly, {a} (duplicable a /\ a) is duplicable. When we
     find a [TyAnd] node, we should be able to assume that the
     constraint holds before continuing. Technically, the type
     {a} (a, (duplicable a /\ a)) is duplicable too; in order
     to be able to prove this, we might need to defer our answer
     at variables. *)

  | TyAnd (_, ty) ->
      (* TEMPORARY too conservative: the constraints are ignored. *)
      is_exclusive env ty

  (* The type c => t is equivalent to t if the constraint holds,
     and is equivalent to unknown otherwise. Thus, this type is
     exclusive only if c holds and t is exclusive. However, we
     do not know if c holds, and the question does not really
     make sense, as it makes the system non-monotonic. Consider
     the following recursive abbreviation:

     alias t = (duplicable t => ref int)

     If t is duplicable, then t is logically equivalent to ref
     int, so t is exclusive. If t is exclusive, then t is not
     duplicable (? presumably t is not bottom), so t is logically
     equivalent to unknown, so t is duplicable. This is completely
     inconsistent!

     In order to avoid these problems, it seems reasonable to say
     that a type of the form c => t is never exclusive, period. *)

  | TyImply _ ->
      false

  | TyBar (ty, _) ->
      is_exclusive env ty

  | TyUnknown
  | TyDynamic
  | TyTuple _
  | TySingleton _
  | TyArrow _
      -> false

  | TyBound _ ->
      Log.error "There should be no bound variables here."

  | TyAnchoredPermission _
  | TyEmpty
  | TyStar _ ->
      Log.error "is_exclusive is defined only at kind type."
      (* TEMPORARY make sure that the kind checking algorithm agrees with this *)


let rec is_duplicable (env : env) (ty : typ) : bool (* TODO lattice point instead of bool *) =
  let ty = modulo_flex env ty in
  match ty with

  | TyOpen _ ->
      (* TODO *)
      (* if free variable: look up fact in environment *)
      (* if parameter of current def: return lattice point for this parameter *)
      (* must be able to identify its number *)
      assert false

  | TyApp (cons, args) ->
      (* TODO should not use [get_fact env], but should use a valuation
	 received as an argument *)
      begin match get_fact env !!cons with
      | Fuzzy _ ->
	  assert false (* cannot happen *)
      | Exclusive
      | Affine ->
	  false
      | Duplicable cons_bitmap ->
	  (* For each argument of the type application... *)
	  List.iteri (fun i ti ->
	    (* The type at [level] may request its [i]-th parameter to be
	     * duplicable. *)
	    if cons_bitmap.(i) then begin
	      (* The answer is yes: the [i]-th parameter for the type
	       * application is [ti] and it has to be duplicable for the
	       * type at [level] to be duplicable too. *)
	      let (_ : bool) = is_duplicable env ti in
	      ()
	    end else begin
	      (* The answer is no: there are no constraints on [ti]. *)
	      ()
	    end
	  ) args;
	  false (* TODO *)
      end

  | TyForall ((binding, _), t') ->
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var (Duplicable [||]) in
      is_duplicable env t'

  | TyExists (binding, t') ->
      (* Be conservative: assume that the quantified variable is affine. *)
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var Affine in
      is_duplicable env t'

  | TyTuple tys ->
      List.fold_left (fun accu ty -> accu && is_duplicable env ty) true tys

  | TyConcreteUnfolded (datacon, fields, _) ->
      let flag, _, _ = def_for_datacon env datacon in
      begin match flag with
      | SurfaceSyntax.Duplicable ->
	  List.fold_left (fun accu field -> accu && is_duplicable_field env field) true fields
      | SurfaceSyntax.Exclusive ->
	  true
      end

  | TyAnd (_, ty) ->
      (* TEMPORARY too conservative: the constraints are ignored. *)
      is_duplicable env ty

  (* The type c => t is logically equivalent to the type t if c holds
     and is logically equivalent to the type unknown otherwise. Because
     unknown is duplicable, the type c => t is duplicable if and only if
     c implies that t is duplicable. Thus, we may assume that c holds,
     just as in the case of TyAnd! Yet, TyAnd and TyImply are still
     different, as the former can be hoisted out, whereas the latter
     cannot. *)

  | TyImply _ ->
      (* TEMPORARY too conservative: the constraints are ignored. *)
      is_duplicable env ty

  | TyBar (ty1, ty2)
  | TyStar (ty1, ty2) ->
      is_duplicable env ty1 && is_duplicable env ty2

  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TySingleton _
  | TyArrow _
      -> true

  | TyAnchoredPermission (_, ty) ->
      is_duplicable env ty

  | TyBound _ ->
      Log.error "There should be no bound variables here."

and is_duplicable_field env = function
  | FieldValue (_, ty)
  | FieldPermission ty ->
      is_duplicable env ty

and conjunction cs =
  List.fold_left (fun accu c -> accu && c) true cs

