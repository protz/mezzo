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
;;


(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

(* Some quantifiers can be instantiated by a user, some cannot, especially those
 * introduced in the desugaring phase. *)
type binding_flavor = CanInstantiate | CannotInstantiate

type type_binding =
    Variable.name * kind * (Lexing.position * Lexing.position)

type typ =
  | TyLocated of typ * Lexing.position * Lexing.position
  | TyTuple of typ list
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
  | TyNameIntro of Variable.name * typ
  | TyConsumes of typ
  | TyBar of typ * typ
  | TyConstraints of duplicity_constraint list * typ

and duplicity_constraint = data_type_flag * typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of Variable.name * typ
  | FieldPermission of typ

and data_type_flag = Exclusive | Duplicable

let ty_equals (v: Variable.name) =
  TySingleton (TyVar v)
;;

let rec flatten_star = function
  | TyStar (t1, t2) ->
      flatten_star t1 @ flatten_star t2
  | TyEmpty ->
      []
  | TyConsumes _ as p ->
      [p]
  | TyAnchoredPermission _ as p ->
      [p]
  | TyLocated (p, _, _) ->
      flatten_star p
  | _ as p ->
      Log.error "[flatten_star] only works for types with kind PERM (%a)"
        Utils.ptag p
;;

let fold_star perms =
  if List.length perms > 0 then
    Hml_List.reduce (fun acc x -> TyStar (acc, x)) perms
  else
    TyEmpty
;;

let rec tunloc = function
  | TyLocated (t, _, _) ->
      tunloc t
  | _ as t ->
      t
;;

let tloc = function
  | TyLocated (_, p1, p2) ->
      (p1, p2)
  | _ ->
      Log.error "[tloc] only works when you know for sure the type is located"
;;

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_lhs =
    Variable.name * type_binding list

type data_type_def_rhs =
    data_type_def_branch list

type abstract_fact = 
  | FExclusive of typ
  | FDuplicableIf of typ list * typ

type data_type_def =
  | Concrete of data_type_flag * data_type_def_lhs * data_type_def_rhs
  | Abstract of data_type_def_lhs * kind * abstract_fact option

(* A data type group is a group of mutually recursive data type definitions. *)

type data_type_group =
    data_type_def list


(* ---------------------------------------------------------------------------- *)

(* Patterns *)

type pattern =
  (* x *)
  | PVar of Variable.name
  (* (x: τ, …) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of (Datacon.name * (Variable.name * pattern) list)
  (* Location information. *)
  | PLocated of pattern * Lexing.position * Lexing.position
  (* x: τ *)
  | PConstraint of pattern * typ


(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = Nonrecursive | Recursive

and expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v *)
  | EVar of Variable.name
  (* let rec f p₁ … pₙ: τ = e₁ and … and v = e₂ in e *)
  | ELet of rec_flag * (pattern * expression) list * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of type_binding list * typ * typ * expression
  (* v.f <- e *)
  | EAssign of expression * Variable.name * expression
  (* v <- Datacon *)
  | EAssignTag of expression * Datacon.name
  (* v.f *)
  | EAccess of expression * Variable.name
  (* assert τ *)
  | EAssert of typ
  (* e e₁ … eₙ *)
  | EApply of expression * expression
  (* e [τ₁, …, τₙ] *)
  | ETApply of expression * typ list
  (* match e with pᵢ -> eᵢ *)
  | EMatch of bool * expression * (pattern * expression) list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of (Datacon.name * (Variable.name * expression) list)
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of bool * expression * expression * expression
  (* e₁; e₂ → desugared as let () = e₁ in e₂ *)
  | ESequence of expression * expression
  | ELocated of expression * Lexing.position * Lexing.position
  | EInt of int
  (* Explanations *)
  | EExplained of expression
  (* Adoption/abandon *)
  | EGive of Variable.name * expression
  | ETake of Variable.name * expression
  (* fail *)
  | EFail


(* ---------------------------------------------------------------------------- *)

(* Top-level declarations *)

type declaration =
  | DMultiple of rec_flag * (pattern * expression) list
  | DLocated of declaration * Lexing.position * Lexing.position

type declaration_group =
  declaration list

type program =
  data_type_group * declaration_group
