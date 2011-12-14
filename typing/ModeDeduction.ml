open Printf

module type MODE = sig
  type mode
  val is_universal: mode -> bool
  val leq: mode -> mode -> bool
  val show: mode -> string
end

module type TYCON = sig
  type t
  val compare: t -> t -> int
  val show: t -> string
end

module Make

  (* The mode constants must form a partial order. *)

  (Mode : MODE)

  (* The type constructors must be equipped with an arbitrary total order
     (which is used only for implementation purposes) and must be printable
     in an unambiguous manner (for error reporting). *)

  (TyCon : TYCON)

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
  | OrderingConstraintHypothesis of mode_constant * mode
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

(* Pretty-printing utilities. *)

(* We assume that the syntax of type applications is based on whitespace,
   as in Haskell and Coq. Perhaps we should instead parameterize this
   module over a printer for ground types. *)

let rec show_ground_type_0 = function
  | TyConApp (tycon, []) ->
      TyCon.show tycon
  | TyConApp (_, _ :: _) as gty ->
      "(" ^ show_ground_type gty ^ ")"

and show_ground_type = function
  | TyConApp (tycon, gtys) ->
      List.fold_left (fun accu gty ->
	accu ^ " " ^ show_ground_type_0 gty
      ) (TyCon.show tycon) gtys

let show_goal = function
  | ModeConstraintGoal (cmode, gty) ->
      sprintf "%s (%s)"
	(Mode.show cmode)
	(show_ground_type gty)

(* ---------------------------------------------------------------------------- *)

(* Functions for deciding whether a context entails a goal. *)

(* Internally, we use an exception to signal that a goal does not hold, and
   construct an error message and explanation. At the very end, we catch
   this exception and return a sum. *)

exception NO of string (* explanation *)

(* [instantiate_mode qmode mode] substitutes the mode constant [qmode]
   for the variable [q] within the mode expression [mode]. *)

let instantiate_mode qmode = function
  | ModeVariable ->
      qmode
  | ModeConstant cmode ->
      cmode

(* [entails toplevel context goal] checks that the set of rules in [context]
   entails the goal [goal]. The Boolean flag [toplevel] is used only when
   constructing an error message: the first line of the message differs
   slightly from the following lines. *)

let rec entails toplevel context (ModeConstraintGoal (qmode, TyConApp (tycon, gtys)) as goal) : unit =

  (* If [qmode] is universal, then the goal is true, regardless of the
     rule that governs [tycon] -- in fact, this rule may not even exist. *)

  if not (Mode.is_universal qmode) then

    (* Find which rule in the context governs the type constructor
       that appears at the head of this ground type. If there is
       no such rule, then the goal is not provable. *)

    try
      try
	let Rule (alphas, hypotheses, _) = TyConMap.find tycon context in
	assert (alphas = List.length gtys); (* otherwise, arity mismatch on [tycon] *)

	(* Within each hypothesis, substitute the mode constant [qmode] for the
	   variable [q] and the ground types [gtys] for the type variables
	   [alphas]. This yields a ground constraint. If it is a mode ordering
	   constraint, check that this constraint is valid. If it is a mode
	   constraint, then it forms a subgoal, whose validity we check by
	   (recursively) invoking [entails]. *)

	List.iter (fun hypothesis ->

	  match hypothesis with
	  | OrderingConstraintHypothesis (cmode1, mode2) ->
	      let cmode2 = instantiate_mode qmode mode2 in
	      if not (Mode.leq cmode1 cmode2) then
		(* This ground mode ordering constraint is invalid. A good
		   error message must not just print this invalid ground
		   constraint, because the user will see that the constraint
		   is invalid but will not see how it is connected to the
		   previous goal. Instead, we must reason in terms of the
		   un-instantiated mode ordering constraint and produce an
		   intuitive explanation in natural language. *)
		begin match mode2 with
		| ModeVariable ->
		    (* This is the expected case. The un-instantiated
		       constraint is [cmode1 <= q]. This means that
		       every type whose head constructor is [tycon]
		       is at least [cmode1], and this is the intuitive
		       reason why it cannot be [cmode2]. *)
		    raise (NO (sprintf "%s\"%s\" is always at least %s,\n\
					so this assertion does not hold.\n"
				       (if toplevel then "" else "But ")
				       (TyCon.show tycon) (Mode.show cmode1)))
		| ModeConstant _ ->
		    (* This case should not arise, because it would mean that the
		       client has constructed a rule with an invalid hypothesis,
		       a rule that is never applicable. Nevertheless, we handle it. *)
		    raise (NO ("This is never the case.\n"))
		end
	  | ModeConstraintHypothesis (mode, alpha) ->
	      let subgoal =
		ModeConstraintGoal (
		  instantiate_mode qmode mode,
		  List.nth gtys alpha
		)
	      in
	      entails false context subgoal

	) hypotheses

      with Not_found ->
	raise (NO (sprintf "%sI know nothing about \"%s\".\n"
		     (if toplevel then "" else "But ")
		     (TyCon.show tycon)))

    with NO explanation ->
      (* Prepend a new line, showing the current goal, in front of the
	 explanation that came up from the recursive call. *)
      raise (NO (sprintf "%s: %s.\n%s"
		   (if toplevel then "I cannot establish" else "This requires")
		   (show_goal goal)
		   explanation))

(* ---------------------------------------------------------------------------- *)

(* There remains to wrap up. *)

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

