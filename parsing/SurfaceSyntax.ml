(** This module defines the abstract syntax of the surface language. *)

(* In principle, very little desugaring is performed on the fly by the
   parser. *)

(* ---------------------------------------------------------------------------- *)

(* Kinds. *)

(* Arrow kinds are not accessible to the user. They are used internally:
   a user-defined algebraic data type constructor receives an arrow kind.
   Thus, even internally, we only use first-order kinds (that is, the
   left-hand argument of an arrow kind is never itself an arrow kind). *)

type kind =
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

(* A small helper function that transforms
 * [κ₁ → ... → κₙ → κ₀] into [[κ₁; ...; κₙ], κ₀] *)
let flatten_kind kind =
  let rec flatten_kind acc = function
    | KArrow (k1, k2) ->
        flatten_kind (k1 :: acc) k2
    | _ as k ->
        acc, k
  in
  let acc, k = flatten_kind [] kind in
  k, List.rev acc


(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

type type_binding =
    Variable.name * kind

type consumes_annotation =
  | Consumes
  | ConsumesAndProduces

type typ =
  | TyTuple of tuple_type_component list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of Variable.name
  | TyConcreteUnfolded of data_type_def_branch
  | TySingleton of typ
  | TyApp of typ * typ
  | TyArrow of typ * typ
  | TyForall of type_binding * typ
  | TyAnchoredPermission of typ * typ
  | TyStar of typ * typ

and tuple_type_component =
    consumes_annotation * tuple_type_component_aux

and tuple_type_component_aux =
  | TyTupleComponentValue of Variable.name option * typ
  | TyTupleComponentPermission of typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of anchored_permission
  | FieldPermission of typ

and anchored_permission =
    Variable.name * typ

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_lhs =
    Variable.name * type_binding list

type data_type_def_rhs =
    data_type_def_branch list

type data_type_flag = Exclusive | Duplicable

type data_type_def =
    data_type_flag * data_type_def_lhs * data_type_def_rhs

(* A data type group is a group of mutually recursive data type definitions. *)

type data_type_group =
    data_type_def list

(* ---------------------------------------------------------------------------- *)

(* Patterns *)

type pattern =
  (* x: τ *)
  | PConstraint of pattern * typ
  (* x *)
  | PVar of Variable.name
  (* (x: τ, …) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of (Datacon.name * (Variable.name * Variable.name) list)
  | PLocated of pattern * Lexing.position * Lexing.position

(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = Nonrecursive | Recursive

(* An inner declaration can appear either in a let-binding or a top-level val
 * binding. The types in the surface syntax and the parsing rules are shared. *)
type inner_declaration =
  (* val x, y = ... *)
  | IValues of pattern * expression
  (* val f t₁ … tₙ: τ = ... where tᵢ is a tuple type *)
  | IFunction of Variable.name * (Variable.name * kind) list * typ list * typ * expression

and expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v *)
  | EVar of Variable.name
  (* let rec f p₁ … pₙ: τ = e₁ and … and v = e₂ in e *)
  | ELet of rec_flag * inner_declaration list * expression
  (*(* fun pat -> expr *)
  | EFun of pattern * expression*)
  (* v.f <- e *)
  | EAssign of expression * Variable.name * expression
  (* e e₁ … eₙ *)
  | EApply of expression * expression
  (* match e with pᵢ -> eᵢ *)
  | EMatch of expression * (pattern * expression) list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of (Datacon.name * (Variable.name * expression) list)
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of expression * expression * expression
  (* e₁; e₂ *)
  | ESequence of expression * expression
  | ELocated of expression * Lexing.position * Lexing.position

(* ---------------------------------------------------------------------------- *)

(* Top-level declarations *)

type declaration =
  | DMultiple of rec_flag * inner_declaration list
  | DLocated of declaration * Lexing.position * Lexing.position

type declaration_group =
  declaration list
