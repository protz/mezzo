(* This file contains our internal syntax for expressions. *)

open Types

(* ---------------------------------------------------------------------------- *)

(* Patterns *)

(* The De Bruijn numbering is defined according to a depth-first traversal of
 * the pattern: the first variable encountered will have index 0, and so on. *)
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

type rec_flag = SurfaceSyntax.rec_flag

type expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v, bound *)
  | EVar of index
  (* v, free *)
  | EPoint of point
  (* let rec pat = expr and pat' = expr' in expr *)
  | ELet of rec_flag * (pattern * expression) list * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of (Variable.name * kind) list * typ list * typ * expression
  (* v.f <- e *)
  | EAssign of expression * Field.name * expression
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
  (* Arithmetic *)
  | EPlus of expression * expression
  | EMinus of expression * expression
  | ETimes of expression * expression
  | EDiv of expression * expression
  | EUMinus of expression
  | EInt of int


(* The grammar below doesn't enforce the “only variables are allowed on the
 * left-hand side of a let rec” rule. We'll see to that later. Here too, the
 * order of the bindings is significant: if the binding is recursive, the
 * variables in all the patterns are collected in order before type-checking the
 * expressions. *)
type declaration =
  | DMultiple of rec_flag * (pattern * expression) list
  | DLocated of declaration * Lexing.position * Lexing.position

type declaration_group =
  declaration list
