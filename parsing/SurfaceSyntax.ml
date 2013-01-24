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

type location = Lexing.position * Lexing.position

let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

(* Some quantifiers can be instantiated by a user, some cannot, especially those
 * introduced in the desugaring phase. *)
type binding_flavor = CanInstantiate | CannotInstantiate

type type_binding =
    Variable.name * kind * (Lexing.position * Lexing.position)

type typ =
  | TyLocated of typ * location
  | TyTuple of typ list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of Variable.name
  | TyQualified of Module.name * Variable.name
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
  | TyAnd of duplicity_constraint list * typ

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

let rec flatten_star p =
  match p with
  | TyStar (t1, t2) ->
      flatten_star t1 @ flatten_star t2
  | TyEmpty ->
      []
  | TyVar _
  | TyConsumes _
  | TyAnchoredPermission _
  | TyApp _ ->
      [p]
  | TyLocated (p, _) ->
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
  | TyLocated (t, _) ->
      tunloc t
  | _ as t ->
      t
;;

let tloc = function
  | TyLocated (_, p) ->
      p
  | _ ->
      Log.error "[tloc] only works when you know for sure the type is located"
;;

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_lhs =
    Variable.name * type_binding list

type data_type_def_rhs =
    data_type_def_branch list

type adopts_clause =
    typ option

type abstract_fact = 
  | FExclusive of typ
  | FDuplicableIf of typ list * typ

type data_type_def =
  | Concrete of data_type_flag * data_type_def_lhs * data_type_def_rhs *
      adopts_clause
  | Abstract of data_type_def_lhs * kind * abstract_fact option

(* A data type group is a group of mutually recursive data type definitions. *)

type data_type_group =
    location * data_type_def list


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
  | PLocated of pattern * location
  (* x: τ *)
  | PConstraint of pattern * typ
  (* p as x *)
  | PAs of pattern * pattern
  (* _ *)
  | PAny


(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = Nonrecursive | Recursive

and expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v *)
  | EVar of Variable.name
  (* M :: v *)
  | EQualified of Module.name * Variable.name
  (* builtin foo *)
  | EBuiltin of string
  (* let rec f p₁ … pₙ: τ = e₁ and … and v = e₂ in e *)
  | ELet of rec_flag * (pattern * expression) list * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of type_binding list * typ * typ * expression
  (* v.f <- e *)
  | EAssign of expression * field * expression
  (* tag of v <- Datacon *)
  | EAssignTag of expression * previous_and_new_datacon
  (* v.f *)
  | EAccess of expression * field
  (* assert τ *)
  | EAssert of typ
  (* e₁ e₂ *)
  | EApply of expression * expression
  (* e [τ₁, …, τₙ] *)
  | ETApply of expression * tapp list
  (* match e with pᵢ -> eᵢ *)
  | EMatch of bool * expression * (pattern * expression) list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … } *)
  | EConstruct of (Datacon.name * (Variable.name * expression) list)
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of bool * expression * expression * expression
  (* e₁; e₂ → desugared as let () = e₁ in e₂ *)
  | ESequence of expression * expression
  | ELocated of expression * location
  | EInt of int
  (* Explanations *)
  | EExplained of expression
  (* Adoption/abandon *)
  | EGive of expression * expression
  | ETake of expression * expression
  | EOwns of expression * expression
  (* fail *)
  | EFail

and field = {
  field_name: Variable.name;
  mutable field_datacon: Datacon.name;
}

and previous_and_new_datacon = {
  (* Initialized by the parser. *)
  new_datacon: Datacon.name;
  (* Uninitialized by the parser. Information later filled in by the type-checker. *)
  mutable previous_datacon: Datacon.name;
}

and tapp =
  | Ordered of typ
  | Named of Variable.name * typ



(* ---------------------------------------------------------------------------- *)

(* Top-level declarations *)

type declaration =
  | DMultiple of rec_flag * (pattern * expression) list
  | DLocated of declaration * location

type declaration_group =
  declaration list

(* TEMPORARY it is not clear why ValueDeclarations carries a *list* of
   declarations, where each declaration can itself be a *list* of
   pattern-definition pairs. Is there redundancy? Also, the scoping
   rules should be clarified (add comments). *)

type toplevel_item =
  | DataTypeGroup of data_type_group
  | ValueDeclarations of declaration_group
  | PermDeclaration of Variable.name * typ
  | OpenDirective of Module.name

(* TEMPORARY I suggest renaming as follows:
   "declaration"       -> "value_definition"
   "ValueDeclarations" -> "ValueDefinitions"
   "PermDeclaration"   -> "ValueDeclaration"
-fpottier *)

(* An implementation will only contain data type groups, value declarations and
 * open directives. *)
type implementation =
  toplevel_item list

(* An interface will only contain data type groups, permission declarations
 * and open directives. *)
type interface =
  toplevel_item list
