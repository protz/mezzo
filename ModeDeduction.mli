(* This module offers machinery for declaring RULES that govern which types
   satisfy which modes and for proving GOALS according to these rules. *)

(* Typical examples of modes are: ``duplicable'', ``exclusive'', ``affine'',
   ``linear''. Modes can be viewed as predicates over types: certain types
   satisfy certain modes. *)

(* Modes are ordered: certain modes represent larger sets of types than
   others. For instance, ``duplicable'' is typically a sub-mode of ``affine'',
   and ``exclusive'' is typically a sub-mode of ``affine''. *)

(* Typical examples of rules include: ``a reference is exclusive'', ``a purely
   functional list is duplicable if its elements are duplicable'', ``a purely
   functional list is affine if its elements are affine'', and so on. *)

(* The building blocks of rules and goals are constraints. We work with two
   kinds of constraints: (a) ordering constraints between modes, of the form
   mode <= mode, where each mode is either a variable or a constant; (b)
   mode constraints, of the form mode(tau), where mode is again a variable
   or a constant, and tau is a type. *)

(* More precisely, a rule is a Horn clause of the following very specific form:

       forall q, forall alphas, hypothesis* <-> head

   A rule is universally quantified over exactly ONE mode variable q and over
   an arbitrary number of type variables alphas. The head MUST be of the form
   
       q (T alphas)

   where T is a type constructor. The number of hypotheses is arbitrary, and
   each hypothesis MUST be

       either a mode ordering constraint: mode <= mode
              (whose only free variable is q)
       or     a mode constraint: mode (alpha)
              (whose free variables are alpha, a member of alphas,
                                    and possibly also q)

*)

(* We assume that rules satisfy the following monotonicity hypothesis: if
   the ground constraint mode1 (tau) is valid, and if mode1 <= mode2 holds,
   then the ground constraint mode2 (tau) is valid as well. In other words,
   in every rule, every hypothesis MUST be covariant with respect to q. In
   practice, this means that hypotheses of the form [q <= mode] are forbidden.
   That is, the left-hand side of an ordering hypothesis must be a constant. *)

(* A context is a set of rules, each of which MUST concern a distinct type
   constructor T. Thus, a rule is really a logical equivalence, not just
   an implication. *)

(* A goal is a mode constraint of the form mode (tau), where tau is a ground
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

: sig

(* ---------------------------------------------------------------------------- *)

(* Syntax for rules and goals. *)

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
  | OrderingConstraintHypothesis of mode_constant * mode (* TEMPORARY force rhs to be a variable *)
  | ModeConstraintHypothesis of mode * type_variable

type hypotheses =
    hypothesis list

type head =
    TyCon.t
      (* This represents q (T alphas). *)
      (* The mode variable q and the type variables alphas are implicit. *)

(* Note that the ordering of the hypotheses within a rule matters: it
   influences the error messages that are produced when a goal does not
   hold. The hypotheses are checked from left to right, so ``simpler''
   hypotheses should be listed first and ``complex'' hypotheses last. *)

type rule =
  | Rule of int * hypotheses * head
      (* length of the list [alphas], hypotheses, head *)

type ground_type =
  | TyConApp of TyCon.t * ground_type list

(* A context is a collection of rules. *)

type context

type goal =
  | ModeConstraintGoal of mode_constant * ground_type

(* ---------------------------------------------------------------------------- *)

(* Functions for constructing contexts. *)

val empty: context
val add: rule -> context -> context

(* ---------------------------------------------------------------------------- *)

(* Functions for deciding whether a context entails a goal. *)

(* [entails context goal] tells whether the set of rules in [context] entails
   the goal [goal]. It returns either [Yes], or [No], accompanied with a
   textual explanation. *)

type result =
  | Yes
  | No of string (* explanation *)

val entails: context -> goal -> result

end

