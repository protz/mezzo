(* This module offers machinery for declaring RULES that govern which types
   satisfy which modes and for proving GOALS according to these rules. *)

(* Typical examples of modes are: ``duplicable'', ``exclusive'', ``affine'',
   ``linear''. Modes can be viewed as predicates over types: certain types
   satisfy certain modes. *)

(* Modes are ordered: certain modes represent larger sets of types than
   others. For instance, ``duplicable'' is typically a sub-mode of ``affine'',
   and ``affine'' is typically a sub-mode of ``linear''. *)

(* Typical examples of rules include: ``a reference is exclusive'', ``a purely
   functional list is duplicable if its elements are duplicable'', ``a purely
   functional list is affine it its elements are affine'', and so on. *)

(* The building blocks of rules and goals are constraints. We work with two
   kinds of constraints: (a) ordering constraints between modes, of the form
   mode <= mode, where each mode is either a variable or a constant; (b)
   mode constraints, of the form mode(tau), where mode is again a variable
   or a constant, and tau is a type. *)

(* More precisely, a rule is a Horn clause of the following very specific form:

       forall q, forall alphas, hypothesis* <-> head

   A rule is universally quantified over exactly ONE mode variable q and over
   an arbitrary number of type variables alphas. The head MUST be of the form
   
       q (T as)

   where T is a type constructor. The number of hypotheses is arbitrary, and
   each hypothesis MUST be

       either a mode ordering constraint mode <= mode
              (whose only free variable is q)
       or     a mode constraint mode alpha
              (whose free variables are alpha, a member of alphas,
                                    and possibly also q)

*)

(* A context is a set of rules, each of which MUST concern a distinct type
   constructor T. Thus, a rule is really a logical equivalence, not just
   an implication. *)

(* A goal is a mode constraint of the form mode tau, where tau is a ground
   type, that is, a type built entirely out of type constructors T. *)

(* ---------------------------------------------------------------------------- *)

(* The code is organized as a functor. It is parameterized over a partially
   ordered set of modes and over a set of type constructors. *)

module Make

  (* The mode constants must form a partial order. *)

  (Mode : sig
    type mode
    val leq: mode -> mode -> bool
    val show: mode -> string
  end)

  (* The type constructors must be equipped with an arbitrary total order
     (which is used only for implementation purposes) and must be printable
     in an unambiguous manner (for error reporting). *)

  (TyCon : sig
      type t
      val compare: t -> t -> int
      val show: t -> string
  end)

= struct

module TyConMap = Map.Make(TyCon)

(* ---------------------------------------------------------------------------- *)

(* Data structures. *)

type mode_constant =
    Mode.mode

type mode =
  | ModeVariable
      (* there is only one mode variable per clause! *)
  | ModeConstant of mode_constant

type type_variable =
    int
      (* a de Bruijn level: leftmost member of [alphas] is zero *)

type hypothesis =
  | OrderingConstraintHypothesis of mode * mode
  | ModeConstraintHypothesis of mode * type_variable

type hypotheses =
    hypothesis list

type head =
    TyCon.t
      (* This represents q (T alphas). *)
      (* The mode variable q and the type variables alphas are implicit. *)

type rule =
  | Rule of int * hypotheses * head
      (* length of the list [alphas], hypotheses, head *)

type ground_type =
  | TyConApp of TyCon.t * ground_type list

(* Internally, a context is a map of type constructors to rules. *)

type context =
  rule TyConMap.t

type goal =
  | ModeConstraintGoal of mode_constant * ground_type

(* ---------------------------------------------------------------------------- *)

(* Functions for constructing contexts. *)

let empty : context =
  TyConMap.empty

let well_scoped_hypothesis alphas = function
  | OrderingConstraintHypothesis (_, _) ->
      true
  | ModeConstraintHypothesis (_, alpha) ->
      0 <= alpha && alpha < alphas

let well_scoped_rule (Rule (alphas, hypotheses, _)) : bool =
  alphas >= 0 &&
  List.for_all (well_scoped_hypothesis alphas) hypotheses

let add (Rule (_, _, tycon) as rule) context =
  (* The client must not attempt to build a context with several rules that
     concern a single type constructor [tycon]. *)
  assert (not (TyConMap.mem tycon context));
  (* The rule should not refer to any type variable that is not in scope. *)
  assert (well_scoped_rule rule);
  (* Insert the rule into the context. *)
  TyConMap.add tycon rule context

(* ---------------------------------------------------------------------------- *)

(* Functions for deciding whether a context entails a goal. *)

exception NO of string

open Printf

let rec show_ground_type = function
  | TyConApp (tycon, gtys) ->
      List.fold_left (fun accu gty ->
	accu ^ " " ^ show_ground_type gty (* TEMPORARY parenthesize! *)
      ) (TyCon.show tycon) gtys

let show_goal = function
  | ModeConstraintGoal (mode, gty) ->
      sprintf "%s (%s)"
	(Mode.show mode)
	(show_ground_type gty)

let instantiate
    (mode : mode_constant)
    (gtys : ground_type list)
    (hypothesis : hypothesis)
    : goal =
  assert false (* TEMPORARY *)



let rec entails toplevel context (ModeConstraintGoal (mode, TyConApp (tycon, gtys)) as goal) : unit =

  (* Find which rule in the context governs the type constructor
     that appears at the head of this ground type. If there is
     no such rule, then the goal is not provable. *)

  try
    let Rule (alphas, hypotheses, _) = TyConMap.find tycon context in
    
    (* Instantiate the parameter q with the mode constant [mode] and the type
       variables [alphas] with the ground types [gtys]. Then, check that every
       sub-goal holds.*)

    assert (alphas = List.length gtys); (* otherwise, arity mismatch on [tycon] *)

    try

      List.iter (fun hypothesis ->
	let subgoal = instantiate mode gtys hypothesis in
	entails false context subgoal
      ) hypotheses

    with NO explanation ->

      let line =
	if toplevel then
	  sprintf "I cannot establish: %s.\n" (show_goal goal)
	else
	  sprintf "This would imply: %s.\n" (show_goal goal)
      in
      raise (NO (line ^ explanation))

  with Not_found ->
    raise (NO (sprintf "But I know nothing about \"%s\".\n" (TyCon.show tycon)))

type result =
  | Yes
  | No of string (* explanation *)

let entails context goal : result =
  try
    entails true context goal;
    Yes
  with NO explanation ->
    No explanation

end

