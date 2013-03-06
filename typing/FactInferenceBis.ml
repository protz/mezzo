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
     be exclusive. I will adopt the convention that [exclusive t] is true
     only when [t] has kind [type]. *)

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

  let meet m1 m2 =
    match m1, m2 with
    | ModeBottom, _
    | _, ModeBottom ->
        ModeBottom
    | ModeAffine, m
    | m, ModeAffine ->
        m
    | _, _ ->
        if m1 = m2 then m1 else ModeBottom

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

  (* The true hypothesis. *)

  let trivial : hypothesis =
    HConjunction ParameterMap.empty

  (* Conjunction of hypotheses. *)

  let conjunction (h1 : hypothesis) (h2 : hypothesis) : hypothesis =
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

  let conjunction_many f xs =
    List.fold_left (fun accu x ->
      conjunction accu (f x)
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
     [duplicable]. *)

  let duplicable (h : hypothesis) : fact =
    ModeMap.total (function
      | ModeDuplicable ->
	  h
      | ModeAffine ->
	  trivial
      | ModeBottom
      | ModeExclusive ->
	  HFalse
    )

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
	  Some (conjunction h1 h2)
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
	  conjunction
	    (ModeMap.find m (List.nth facts i))
	    accu
        ) hs trivial
    ) fact

end

(* ---------------------------------------------------------------------------- *)

open TypeCore
open Types

(* ---------------------------------------------------------------------------- *)

(* This glue code adapts the type [TypeCore.fact], used in the environment, to
   our internal representation of modes and facts, which is different. *)

(* TEMPORARY ultimately, the environment itself should be adapted *)

let adapt_mode (f : TypeCore.fact) : mode =
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

let adapt_fact (f : TypeCore.fact) : Fact.fact =
  match f with
  | Exclusive ->
      Fact.constant ModeExclusive
  | Affine ->
      Fact.constant ModeAffine
  | Duplicable bitmap ->
      (* This is a bit laborious... *)
      let hs = ref ParameterMap.empty in
      Array.iteri (fun i bit ->
	if bit then
	  hs := ParameterMap.add i ModeDuplicable !hs
      ) bitmap;
      Fact.duplicable (Fact.HConjunction !hs)
  | Fuzzy _ ->
      (* no longer used *)
      assert false

let adapt_flag (flag : SurfaceSyntax.data_type_flag) : mode =
  match flag with
  | SurfaceSyntax.Exclusive ->
      ModeExclusive
  | SurfaceSyntax.Duplicable ->
      ModeDuplicable

let unadapt_fact (arity : int) (parameters : int VarMap.t) (f : Fact.fact) : TypeCore.fact =
  (* Every type should be unconditionally affine. *)
  assert (match ModeMap.find ModeAffine f with
  | Fact.HFalse ->
      false
  | Fact.HConjunction hs ->
      Fact.is_trivial hs
  );
  (* Now, check whether this type can be duplicable/exclusive. *)
  match ModeMap.find ModeDuplicable f, ModeMap.find ModeExclusive f with
  | Fact.HFalse, Fact.HFalse ->
      (* Neither. *)
      Affine
  | Fact.HFalse, Fact.HConjunction hs ->
      (* It can be exclusive. Check that this is unconditional. *)
      assert (Fact.is_trivial hs);
      Exclusive
  | Fact.HConjunction hs, Fact.HFalse ->
      (* It can be duplicable. Translate the conditions back to a
	 parameter bitmap. *)
      let bitmap = Array.make arity false in
      VarMap.iter (fun _ i ->
	let m = try ParameterMap.find i hs with Not_found -> ModeAffine in
	match m with
	| ModeAffine ->
	    ()
	| ModeDuplicable ->
	    bitmap.(i) <- true
	| ModeExclusive ->
	    Log.error "Unexpected fact format! exclusive a => duplicable (...)"
	| ModeBottom ->
	    Log.error "Unexpected fact format! bottom a => duplicable (...)"
      ) parameters;
      Duplicable bitmap
  | Fact.HConjunction _, Fact.HConjunction _ ->
      Log.error "Unexpected fact format! this type is duplicable and exclusive"

(* ---------------------------------------------------------------------------- *)

type world = {
  variables: unit VarMap.t;
  valuation: var -> Fact.fact;
  parameters: Parameter.t VarMap.t;
  env: env;
  assumptions: mode VarMap.t;
}

let hoist_mode_assumptions (_v : var) (_ty : typ) : mode =
  ModeAffine (* TEMPORARY *)

let assume w ((flag, ty) : duplicity_constraint) : world =
  let m = adapt_flag flag in
  let ty = modulo_flex w.env ty in
  match ty with

  | TyOpen v when is_rigid w.env v && VarMap.mem v w.assumptions ->

      (* [v] is present in [assumptions], so [v] is local. Install
         a new assumption about it. We take the meet of the old
         and new assumptions. *)
      let assumptions =
        VarMap.add v (Mode.meet m (VarMap.find v w.assumptions)) w.assumptions
      in
      { w with assumptions }

  | _ ->
      (* TEMPORARY! treat the other cases *)
      w

let assume w cs =
  List.fold_left assume w cs

(* ---------------------------------------------------------------------------- *)

(* Inferring a fact about a type. *)

(* TEMPORARY document *)
(* [VarMap] supports rigid variables only. *)

let rec infer (w : world) (ty : typ) : Fact.fact =
  let ty = modulo_flex w.env ty in
  match ty with

  (* TEMPORARY if the environment adopts our format for facts, then we can
     merge [env] and [assumptions], and cases 1 and 3 below become a single
     case. *)

  (* A type variable, represented by [TyOpen _], could be a local variable
     (e.g. introduced by a universal quantifier which we have just entered)
     or a parameter or a pre-existing variable. In the first two cases, it
     must be rigid, I think; in the last case, it could be rigid or flexible. *)

  | TyOpen v when is_rigid w.env v && VarMap.mem v w.assumptions ->

      (* [v] is present in [assumptions], so we are in the first case:
	 [v] is local. Our assumptions tell us that [v] has mode [m]. We
	 produce the fact [m], without any hypotheses on the parameters. *)
      let m : mode = VarMap.find v w.assumptions in
      Fact.constant m

  | TyOpen v when is_rigid w.env v && VarMap.mem v w.parameters ->

      (* [v] is present in [parameters], so we are in the second case:
	 [v] is a parameter [p]. We produce a fact of the form [m p => m],
	 for every mode [m]. This means ``for every mode [m], if the
	 parameter [p] has mode [m], then this type has mode [m].'' *)
      let p : Parameter.t = VarMap.find v w.parameters in
      Fact.parameter p

  | TyOpen v ->

      (* [v] is not present in [assumptions] or [parameters], so it is
	 external. We look up the environment in order to obtain a mode [m]
	 for [v], and turn it into a constant fact [m]. *)
      Fact.constant (adapt_mode (get_fact w.env v))

  (* In a type application, the type constructor [v] cannot be local and
     cannot be a parameter (due to restrictions at the kind level). It
     also cannot be flexible. There are two cases to consider: either it
     is part of the set [variables], i.e. it is involved in the current
     fixed point computation; or it is older, and is defined in [env]. *)

  | TyApp (v, args) ->
      let v = !!v in
      (* Get a fact for [v]. *)
      let fact =
	if VarMap.mem v w.variables then
	  (* [v] is a variable. Obtain a fact for it through the current
	     valuation. *)
	  w.valuation v
	else
	  (* [v] is older. Obtain a fact for it through the environment. *)
	  adapt_fact (get_fact w.env v)
      in
      (* Infer facts for the arguments. We must be careful because not
	 all arguments have kind [type] or [perm], and fact inference
	 works only at these kinds. We infer a trivial fact at kind
	 [term], which will not be used. *)
      let facts = infer_many w (get_kind w.env v) args in
      (* Compose these facts in order to obtain a fact for the type
	 application. *)
      Fact.compose fact facts

  (* When we find a universal or existential quantifier, we enter it. The
     quantified variable becomes local, and is added to [assumptions]. *)

  (* In the universal case, I believe that we are free to associate this
     variable with the most precise mode, [Mode.bottom]. This is logically
     equivalent to replacing this variable with the type [TyBottom]. *)

  (* In the existential case, it appears, at first sight, that we must
     associate this variable with the least precise mode, [Mode.top].
     However, that would be a bit over-conservative. We would like to
     be able to establish the following facts:

       exclusive  ({a} (exclusive  a /\ a))
       duplicable ({a} (duplicable a /\ a))

     and, slightly more difficult,

       duplicable ({a} (a, (duplicable a /\ a)))

     This suggests that, when we enter an existential quantifier, we must
     descend in the structure and look for assumption about the quantified
     variable that can be hoisted out. *)

  | TyForall ((binding, _), ty) ->
      let env, ty, v = bind_rigid_in_type w.env binding ty in
      let assumptions = VarMap.add v Mode.bottom w.assumptions in
      infer { w with env; assumptions } ty

  | TyExists (binding, ty) ->
      let env, ty, v = bind_rigid_in_type w.env binding ty in
      let m = hoist_mode_assumptions v ty in
      let assumptions = VarMap.add v m w.assumptions in
      infer { w with env; assumptions } ty

  (* A type of the form [c /\ t], where [c] is a mode constraint and [t]
     is a type, can be thought of as a pair of a proof of [c] and a value
     of type [t]. Certainly, if [t] is duplicable, then [c /\ t] is too,
     because proofs don't exist at runtime and are duplicable. Similarly,
     for every mode [m], it [t] has mode [m], then [c /\ t] has mode [m]. *)

  (* In the common case where the constraint [c] bears upon a variable [a]
     that was existentially quantified above, we have already taken this
     constraint into account via [hoist_mode_assumptions]. *)

  (* In the uncommon case where the constraint [c] bears upon a non-variable
     type, we could in principle try to destructure this constraint. For the
     moment, this is not done. TEMPORARY? *)

  (* We might also find a constraint that bears on a parameter; we should it
     take it into account. TEMPORARY *)

  | TyAnd (_, ty) ->
      infer w ty

  (* The type [c => t], where [c] is a mode constraint and [t] is a type,
     represents [t] if [c] holds and [unknown] otherwise. Thus, in order
     to prove that [c => t] has mode [m], we must prove that [t] has mode
     [m] under the assumption [c] and that [unknown] has mode [m]. (We
     do not assume the negation of [c], as that would make the system
     non-monotonic.) *)

  (* TEMPORARY think about constraints on parameters or on structured types,
     etc. *)

  | TyImply (cs, ty) ->
      Fact.join
	(infer (assume w cs) ty)
	(infer w TyUnknown)

  (* We could prove that a tuple or record is [bottom] as soon as one of
     its components is bottom, but there is no motivation to do so. *)

  | TyConcreteUnfolded (datacon, fields, _) ->
      (* The [adopts] clause has no impact. *)
      let flag, _, _ = def_for_datacon w.env datacon in
      infer_concrete w flag fields

  | TyTuple tys ->
      Fact.duplicable (
	Fact.conjunction_many (fun ty ->
	  ModeMap.find ModeDuplicable (infer w ty)
	) tys
      )

  (* [TyBar] is duplicable if both of its components are duplicable,
     and is exclusive if its left-hand component is exclusive. *)

  | TyBar (ty1, ty2) ->
      Fact.join
	(infer w ty1)
	(Fact.allow_exclusive (infer w ty2))

  (* [TyStar] is duplicable if both of its components are duplicable. *)

  | TyStar (ty1, ty2) ->
      Fact.join
	(infer w ty1)
	(infer w ty2)

  (* [x @ t] is duplicable if [t] is duplicable. It is not considered
     exclusive. The use of [disallow_exclusive] is probably not essential
     here, but seems clean/prudent. *)

  | TyAnchoredPermission (_, ty) ->
      Fact.disallow_exclusive (infer w ty)

  (* [unknown], [dynamic], [empty], [=x], [t -> u] are duplicable. *)

  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TySingleton _ 
  | TyArrow _ ->
      Fact.constant ModeDuplicable

  | TyBound _ ->
      Log.error "There should be no bound variables here."

and infer_concrete w flag fields =
  match flag with
  | SurfaceSyntax.Duplicable ->
      (* When a data type is defined as immutable, it is duplicable
	 if and only if its fields are duplicable. It is definitely
	 not exclusive. *)
      Fact.duplicable (
	Fact.conjunction_many (fun field ->
	  ModeMap.find ModeDuplicable (infer_field w field)
	) fields
      )
  | SurfaceSyntax.Exclusive ->
      (* When a data type is defined as exclusive, it is exclusive
	 regardless of its fields. *)
      Fact.constant ModeExclusive

and infer_field w field =
  match field with
  | FieldValue (_, ty)
  | FieldPermission ty ->
      infer w ty

and infer_many w kind args =
  match kind, args with
  | _, [] ->
      []
  | KArrow (kind, kinds), arg :: args ->
      begin match kind with
      | KTerm ->
	  (* Do not call [infer] at kind [term]. Instead, provide
	     a dummy fact. *)
	  Fact.bottom
      | KType
      | KPerm ->
	  infer w arg
      | KArrow _ ->
	  assert false (* higher-order kind *)
      end
      :: infer_many w kinds args
  | _, _ ->
      assert false (* kind mismatch *)

(* ---------------------------------------------------------------------------- *)

(* The main fixed point computation. *)

let analyze_data_types (env : env) (variables : var list) : env =

  (* Make it a set of variables. *)

  let variables =
    List.fold_left (fun accu v ->
      VarMap.add v () accu
    ) VarMap.empty variables
  in

  (* Tie the knot. *)

  let module F =
    Fix.Make(IVarMap)(Fact)
  in
  let fixpoint : var -> Fact.fact =
    F.lfp (fun (v : var) ->
      (* Here, [v] is an algebraic data type, for which we would like
	 to infer a fact. *)
      match get_definition env v with
      | None ->
	  Log.error "A data type should have a definition."
      | Some (None, _) ->
	  (* This is an abstract type. Its fact is declared by the user.
	     In that case, the code in the [DataTypeGroup] has already
	     taken care of entering an appropriate fact in the environment.
	     We just look it up. *)
	  let f = adapt_fact (get_fact env v) in
	  fun (_ : F.valuation) -> f
      | Some (Some (flag, branches, clause), _) ->
	  fun valuation ->
	    (* Bind the parameters. Drop the [adopts] clause. *)
	    let env, parameters, branches, _ =
	      bind_datacon_parameters env (get_kind env v) branches clause
	    in
	    (* Construct a map of the parameters to their indices. The ordering
	       matters, of course; it is used in [compose] when matching formal
	       and actual parameters. *)
	    let parameters =
	      MzList.fold_lefti (fun i accu v ->
		VarMap.add v i accu
	      ) VarMap.empty parameters
	    in
	    (* Construct a world. *)
	    let w = {
	      variables;
	      valuation;
	      parameters;
	      env;
	      assumptions = VarMap.empty
	    } in
	    (* The right-hand side of the algebraic data type definition can be
	       viewed as a sum of records. *)
	    Fact.join_many (fun branch ->
	      let _, fields = branch in
	      infer_concrete w flag fields
	    ) branches
    )
  in

  (* For each algebraic data type [v], compute a fact, and update the
     environment with this fact. *)

  VarMap.fold (fun v () env ->
    (* Repeating the [match] construct is inelegant; I am doing this
       only to obtain [arity] and [parameters], which I need in order
       to call [unadapt_fact]. TEMPORARY *)
    match get_definition env v with
    | None
    | Some (None, _) ->
        env
    | Some (Some (_, branches, clause), _) ->
	let _, parameters, _, _ =
	  bind_datacon_parameters env (get_kind env v) branches clause
	in
	let arity = List.length parameters in
	let parameters =
	  MzList.fold_lefti (fun i accu v ->
	    VarMap.add v i accu
	  ) VarMap.empty parameters
	in
	let f =
	  unadapt_fact arity parameters (fixpoint v)
	in
	set_fact env v f
  ) variables env

(* ---------------------------------------------------------------------------- *)

(* Accessors. *)

let analyze_type (env : env) (ty : typ) : Fact.fact =
  (* Construct a world. Only the [env] component is non-trivial. *)
  let w = {
    variables = VarMap.empty;
    valuation = (fun _ -> assert false); (* will not be called *)
    parameters = VarMap.empty;
    env;
    assumptions = VarMap.empty
  } in
  (* Go. *)
  infer w ty

let has_mode (m : mode) (env : env) (ty : typ) : bool =
  match ModeMap.find m (analyze_type env ty) with
  | Fact.HFalse ->
      false
  | Fact.HConjunction hs ->
      assert (Fact.is_trivial hs);
      true

let is_duplicable =
  has_mode ModeDuplicable

let is_exclusive =
  has_mode ModeExclusive
  
let analyze_type env ty : TypeCore.fact =    
  unadapt_fact 0 VarMap.empty (analyze_type env ty)
  (* TEMPORARY since this is a parameterless fact, it is in fact
     just a mode, or maybe a conjunction of modes. Perhaps we
     should publish it this way? Or perhaps we could keep this
     function private, as it is not used often. *)
