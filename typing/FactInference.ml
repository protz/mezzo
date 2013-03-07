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
open Fact
open DataTypeFlavor
open TypeCore
open Types

(* ---------------------------------------------------------------------------- *)

type world = {
  variables: unit VarMap.t;
  valuation: var -> Fact.fact;
  parameters: parameter VarMap.t;
  env: env;
  assumptions: mode VarMap.t;
}

let hoist_mode_assumptions (_v : var) (_ty : typ) : mode =
  ModeAffine (* TEMPORARY *)

(* TEMPORARY connection with [Permission.add_constraints] *)
let assume w ((m, ty) : mode_constraint) : world =
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
      let p : parameter = VarMap.find v w.parameters in
      Fact.parameter p

  | TyOpen v ->

      (* [v] is not present in [assumptions] or [parameters], so it is
	 external. We look up the environment in order to obtain a fact
	 for [v]. *)
      get_fact w.env v

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
	  get_fact w.env v
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
	Fact.conjunction (fun ty ->
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
  | Immutable ->
      (* When a data type is defined as immutable, it is duplicable
	 if and only if its fields are duplicable. It is definitely
	 not exclusive. *)
      Fact.duplicable (
	Fact.conjunction (fun field ->
	  ModeMap.find ModeDuplicable (infer_field w field)
	) fields
      )
  | Mutable ->
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
	  let f = get_fact env v in
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
    match get_definition env v with
    | None
    | Some (None, _) ->
        (* Skip abstract types. There is nothing to do in this case,
	   and furthermore, an abstract type could have kind [term],
	   in which case inferring a fact for it does not make sense. *)
        env
    | Some (Some _, _) ->
        (* This data type has a definition, hence it has kind [type]
	   or [perm]. Inferring a fact for it makes sense. *)
	set_fact env v (fixpoint v)
  ) variables env

(* ---------------------------------------------------------------------------- *)

(* Accessors. *)

(* TEMPORARY perhaps we could keep this function private, as it is
   not used often. *)

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
      (* This fact should have arity 0. *)
      assert (ParameterMap.cardinal hs = 0);
      true

let is_duplicable =
  has_mode ModeDuplicable

let is_exclusive =
  has_mode ModeExclusive
  
