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
open Hoist

(* ---------------------------------------------------------------------------- *)

(* Adding a new hypothesis to the environment. *)

let assume (env : env) ((m, ty) : mode_constraint) : env =
  (* We assume that [ty] has kind [type] or [perm]. *)
  (* Turn the mode [m] into a fact of arity 0. *)
  let fact = Fact.constant m in
  let ty = modulo_flex env ty in
  match ty with
  | TyOpen v ->
      set_fact env v (Fact.meet fact (get_fact env v))
    | _ ->
        (* We don't know how to extract meaningful information here, so we're
         * just not doing anything about the constraint we just learned about.
         * This could (maybe) be improved. TEMPORARY *)
        env

(* ---------------------------------------------------------------------------- *)

(* When we analyze an algebraic data type definition, we maintain not only an
   environment, as usual, but also some information about the current fixed
   point computation. We refer to this collection of information as a world. *)

type world = {
  (* The environment. *)
  env: env;
  (* The data type constructors that are being defined, and for which we are
     currently attempting to compute a least valid fact. *)
  variables: unit VarMap.t;
  (* The current valuation of the fixed point computation. It maps each of
     the above [variables] to its current fact. *)
  valuation: var -> Fact.fact;
  (* The parameters of the particular algebraic data type that we are
     currently descending into. *)
  parameters: parameter VarMap.t;
}

(* When we are not in the process of computing a fixed point, [variables]
   is empty, so [valuation] becomes irrelevant; and [parameters] is empty
   as well. *)

(* ---------------------------------------------------------------------------- *)

(* A wrapper for [assume]. *)

let assumew (w : world) (c : mode_constraint) : world =
  { w with env = assume w.env c }

(* ---------------------------------------------------------------------------- *)

(* Inferring a fact about a type. *)

(* This code is used both during and after the fixed point computation. The
   type [ty] must have kind [type] or [perm]. We infer a fact whose arity
   corresponds to the current number of parameters. *)

let rec infer (w : world) (ty : typ) : Fact.fact =
  let ty = modulo_flex w.env ty in
  match ty with

  (* A type variable, represented by [TyOpen _], could be a local variable
     (e.g. introduced by a universal quantifier which we have just entered)
     or a parameter or a pre-existing variable. In the first two cases, it
     must be rigid, I think; in the last case, it could be rigid or flexible. *)

  (* We distinguish only two cases: either [v] is a parameter, or it is not.
     In fact, regardless of this distinction, we always look up the
     environment in order to find an assumption about [v]. Additionally, if
     [v] is a parameter, then we construct a fact of the form [m p => m], for
     every mode [m], which means ``for every mode [m], if the parameter [p]
     has mode [m], then this type has mode [m].'' We take the meet of these
     two facts, since both are true. The meet is well-defined when its
     left-hand argument has arity zero, which is the case here, as the fact
     stored in the environment for a variable of kind [type] or [perm] always
     has arity zero. *)

  | TyOpen v ->

      (* Always look up the environment. *)
      let fact1 = get_fact w.env v in

      (* Check whether [v] is a parameter, and if so, create a more precise
	 fact. Note: [VarMap] supports rigid variables only, hence the check
	 in two steps. *)
      if is_rigid w.env v && VarMap.mem v w.parameters then
	let p : parameter = VarMap.find v w.parameters in
	let fact2 = Fact.parameter p in
	Fact.meet fact1 fact2
      
      else
	fact1

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
     quantified variable becomes local, and a fact about it is (possibly)
     assumed. *)

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
      bind_assume_infer w binding ty Mode.bottom

  | TyExists (binding, ty) ->
      bind_assume_infer w binding ty Mode.top

  (* A type of the form [c /\ t], where [c] is a mode constraint and [t]
     is a type, can be thought of as a pair of a proof of [c] and a value
     of type [t]. Certainly, if [t] is duplicable, then [c /\ t] is too,
     because proofs don't exist at runtime and are duplicable. Similarly,
     for every mode [m], it [t] has mode [m], then [c /\ t] has mode [m]. *)

  (* Furthermore, since we have a proof of [c], we may assume that [c]
     holds while examining [t]. Because we hoist constraints up to the
     nearest quantifier, they will thus (often) be assumed as early as
     possible. *)

  | TyAnd (c, ty) ->
      infer (assumew w c) ty

  (* The type [c => t], where [c] is a mode constraint and [t] is a type,
     represents [t] if [c] holds and [unknown] otherwise. Thus, in order
     to prove that [c => t] has mode [m], we must prove that [t] has mode
     [m] under the assumption [c] and that [unknown] has mode [m]. (We
     do not assume the negation of [c], as that would make the system
     non-monotonic.) *)

  (* Since [hoist] does not hoist constraints out of [TyImply] constructs,
     we should (for completeness) invoke it again here. This is certainly
     not essential in practice. *)

  | TyImply (c, ty) ->
      Fact.join
	(infer (assumew w c) (hoist w.env ty))
	(infer w TyUnknown)

  (* We could prove that a tuple or record is [bottom] as soon as one of
     its components is bottom, but there is no motivation to do so. *)

  | TyConcreteUnfolded branch ->
      let flavor = flavor_for_branch w.env branch in
      infer_concrete w flavor branch.branch_fields

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

and infer_unresolved_branch w branch =
  (* The [adopts] clause has no impact. The name of the data
     constructor does not matter, nor the algebraic data type
     definition to which it belongs; only the [flavor] of this
     branch, and the fields, matter. *)
  infer_concrete w branch.branch_flavor branch.branch_fields

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

and bind_assume_infer w binding ty (m : mode) : fact =
  (* Introduce a new rigid variable. *)
  let env, ty, v = bind_rigid_in_type w.env binding ty in
  (* If this variable has kind [type] or [perm], assume that
     it has mode [m]. An appropriate mode can sometimes be
     found by inspection of the type, so [m] is parameterized
     with [v] and [ty]. *)
  let (_, kind, _) = binding in
  let env =
    match kind with
    | KType
    | KPerm ->
	assume env (m, TyOpen v)
    | KTerm ->
        env
    | KArrow _ ->
        assert false
  in
  (* Hoist the mode constraints that might be buried down inside [ty]
     to the root. This may allow us to assume these constraints right
     away, instead of finding them (too late) when we reach them. *)
  let ty = hoist env ty in
  (* Continue. *)
  infer { w with env } ty

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
      | Some (Some branches, _) ->
	  fun valuation ->
	    (* Bind the parameters. *)
	    let env, parameters, branches =
	      bind_datacon_parameters env (get_kind env v) branches
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
	    } in
	    (* The right-hand side of the algebraic data type definition can be
	       viewed as a sum of records. *)
	    Fact.join_many (infer_unresolved_branch w) branches
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
  
