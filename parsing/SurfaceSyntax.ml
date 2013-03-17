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

(* Field names are just variable names. These two namespaces cannot be
   statically distinguished (due to the possibility of punning). *)

module Field =
  Variable

(* ---------------------------------------------------------------------------- *)

(* Information about data constructors. *)

(* Data constructor definitions should be viewed as generative. That is, when
   a type definition [data t = T { ... }] is processed, a ``fresh'' data
   constructor information record is internally created, to which the name [T]
   becomes bound. If we later process the type definition [data u = T { ... }],
   then a second information record is internally created, to which the name
   [T] now becomes bound. Thus, at this point, we have two logically distinct
   data constructors, only one of which can be referred to by name. *)

(* A data constructor information record could in principle contain a unique
   identifier; it doesn't, because we don't need it. Physical equality of
   data constructor information records gives us a meaningful notion of
   equality. *)

(* We maintain the following information about every data constructor. *)

type datacon_info = {
  (* Its unqualified name (used e.g. by [Interpreter.print_value]). *)
  datacon_name: string;
  (* Its arity (i.e., number of fields). *)
  datacon_arity: int;
  (* Its integer index within its data type definition. *)
  datacon_index: int;
  (* A map of field names to field indices. *)
  datacon_fields: int Field.Map.t;
}

(* ---------------------------------------------------------------------------- *)

(* A name can be either unqualified, [x], or qualified with a module name,
   [m::x]. This holds for variables (of arbitrary kind: term, type, etc.)
   and for data constructors. *)

type 'a maybe_qualified =
  | Unqualified of 'a
  | Qualified of Module.name * 'a

(* ---------------------------------------------------------------------------- *)

(* References to data constructors. *)

(* In the surface syntax, a reference to a data constructor is just a
   (possibly qualified) name. This is what the parser produces. When the
   type-checker runs, it augments this information with a pointer to the
   [datacon_info] record that this reference denotes. This later allows the
   compiler to work with an unambiguous syntax. *)

type datacon_reference = {
  (* The (unqualified or qualified) name, as found in the program. *)
  datacon_unresolved: Datacon.name maybe_qualified;
  (* The information record that this name was found to denote. This
     field is not initialized by the parser; it is later filled in
     by the type-checker, which explains why it is a mutable option. *)
  mutable datacon_info: datacon_info option;
}

(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

open Kind

type location = Lexing.position * Lexing.position

let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

(* Some quantifiers can be instantiated by a user, some cannot, especially those
 * introduced in the desugaring phase. *)
type binding_flavor = CanInstantiate | CannotInstantiate

type type_binding =
    Variable.name * kind * (Lexing.position * Lexing.position)

type variance = Invariant | Covariant | Contravariant | Bivariant

type type_binding_with_variance = variance * type_binding

type typ =
  | TyLocated of typ * location
  | TyTuple of typ list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of Variable.name maybe_qualified
  | TyConcreteUnfolded of (datacon_reference * data_field_def list)
  | TySingleton of typ
  | TyApp of typ * typ
  | TyArrow of typ * typ
  | TyForall of type_binding * typ
  | TyExists of type_binding * typ
  | TyAnchoredPermission of typ * typ
  | TyStar of typ * typ
  | TyNameIntro of Variable.name * typ
  | TyConsumes of typ
  | TyBar of typ * typ
  | TyAnd of mode_constraint * typ
  | TyImply of mode_constraint * typ

and mode_constraint = Mode.mode * typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of Field.name * typ
  | FieldPermission of typ

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_lhs =
    Variable.name * type_binding_with_variance list

type data_type_def_rhs =
    data_type_def_branch list

type adopts_clause =
    typ option

type single_fact = 
  | Fact of mode_constraint list * mode_constraint

type fact =
    single_fact list

type data_type_def =
  | Concrete of DataTypeFlavor.flavor * data_type_def_lhs * data_type_def_rhs *
      adopts_clause
  | Abstract of data_type_def_lhs * kind * fact

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
  | PConstruct of (datacon_reference * (Field.name * pattern) list)
  (* Location information. *)
  | PLocated of pattern * location
  (* x: τ *)
  | PConstraint of pattern * typ
  (* p as x *)
  | PAs of pattern * Variable.name
  (* _ *)
  | PAny


(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = Nonrecursive | Recursive

and expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v or M :: v *)
  | EVar of Variable.name maybe_qualified
  (* builtin foo *)
  | EBuiltin of string
  (* let rec f p₁ … pₙ: τ = e₁ and … and v = e₂ in e *)
  | ELet of rec_flag * (pattern * expression) list * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of type_binding list * typ * typ * expression
  (* v.f <- e *)
  | EAssign of expression * field * expression
  (* tag of v <- Datacon *)
  | EAssignTag of expression * datacon_reference * tag_update_info
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
  | EConstruct of (datacon_reference * (Field.name * expression) list)
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

and tag_update_info = {
  (* Uninitialized by the parser. Information later filled in by the type-checker. *)
  mutable is_phantom_update: bool option;
}

and field = {
  field_name: Field.name;
  (* Uninitialized by the parser. Information later filled in by the type-checker. *)
  mutable field_offset: offset option;
}

and offset =
  int

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

(* ---------------------------------------------------------------------------- *)

(* The following function translates a type to a pattern. *)

(* Note in [EFun] above, the argument is described by a type. This function
   allows viewing the argument as a pattern. In fact, this provides a definition
   of which names can be referred to by the function body. *)

let rec type_to_pattern (ty : typ) : pattern =
  match ty with

  (* A structural type constructor is translated to the corresponding
     structural pattern. *)

  | TyTuple tys ->
      PTuple (List.map type_to_pattern tys)

  | TyConcreteUnfolded (datacon, fields) ->
      let fps =
	List.fold_left (fun fps field ->
	  match field with
          | FieldValue (f, ty) -> (f, type_to_pattern ty) :: fps
          | FieldPermission _  -> fps
	) [] fields in
      PConstruct (datacon, fps)

  (* A name introduction gives rise to a variable pattern. *)

  | TyNameIntro (x, ty) ->
      PAs (type_to_pattern ty, x)

  (* Keep locations. *)

  | TyLocated (ty, loc) ->
      PLocated (type_to_pattern ty, loc)

  (* Pass (go down into) the following constructs. *)

  | TyAnd (_, ty)
  | TyConsumes ty
  | TyBar (ty, _) ->
      type_to_pattern ty

  (* Stop at (do not go down into) the following constructs. *)

  (* We could perhaps allow going down into [TyExists]. This would
     make it possible to name the components of an existential
     package. However, our convention that, in the absence of
     [consumes], a permission that is requested is also returned,
     raises a problem. If I request the permission [x @ t], inside
     an existential package that quantifies [t], what am I promising
     to return? I can't promise to return [x @ t] because [t] is not
     bound in the return type. For this reason, it seems preferable,
     at least for the moment, to adopt the convention that we do not
     look for name introductions inside an existential quantifier. *)

  | TyForall _
  | TyExists _
  | TyImply _
  | TyUnknown
  | TyArrow _ 
  | TySingleton _
  | TyDynamic
  | TyApp _
  | TyVar _ ->
      PAny

  (* The following cases should not arise. *)

  | TyEmpty
  | TyStar _
  | TyAnchoredPermission _ ->
      (* Type of kind PERM, where a type of kind TERM was expected. In
	 principle, this should not happen, except during kind checking,
         where it could happen if the type is ill-kinded. We must return
         silently, and an error will be signaled by the kind checking
	 algorithm. *)
      PAny

(* ---------------------------------------------------------------------------- *)

(* Auxiliary functions for the type [maybe_qualified]. *)

let print_maybe_qualified print = function
  | Unqualified x ->
      print x
  | Qualified (m, x) ->
      Module.print m ^ "::" ^ print x

