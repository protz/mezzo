(* This file contains our internal syntax for expressions. *)

open Types

(* ---------------------------------------------------------------------------- *)

(* Patterns *)

type pattern =
  (* x: τ *)
  | PConstraint of pattern * typ
  (* x *)
  | PVar of Variable.name
  (* (x₁, …, xₙ) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of Datacon.name * (Field.name * Variable.name) list
  | PLocated of pattern * Lexing.position * Lexing.position

(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = Nonrecursive | Recursive

type expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v *)
  | EVar of Variable.name
  (* let rec pat = expr and pat' = expr' in expr *)
  | ELet of rec_flag * (pattern * expression list) * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of Variable.name * (Variable.name * kind) list * typ list * typ * expression
  (* v.f <- e *)
  | EAssign of Variable.name * Field.name * expression
  (* e e₁ … eₙ *)
  | EApply of expression * expression list
  (* match e with pᵢ -> eᵢ *)
  | EMatch of expression * (pattern * expression) list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of Datacon.name * (Field.name * expression) list
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of expression * expression * expression
  (* e₁; e₂ *)
  | ESequence of expression * expression
  | ELocated of expression * Lexing.position * Lexing.position

(* The grammar below doesn't enforce the “only variables are allowed on the
 * left-hand side of a let rec” rule. We'll see to that later. *)
type declaration =
  | DMultiple of rec_flag * (pattern * expression list)
  | DLocated of declaration * Lexing.position * Lexing.position

type declaration_group =
  declaration list
