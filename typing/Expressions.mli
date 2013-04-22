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

(** This module defines the syntax of expressions, as manipulated by the
   type-checker. This module also defines various expression-specific
   manipulation functions, esp. w.r.t. binders. *)

open Kind
open TypeCore


(* -------------------------------------------------------------------------- *)

(** {1 The definition of expressions} *)

type tag_update_info = SurfaceSyntax.tag_update_info

type field = SurfaceSyntax.field

(** The type of patterns. We don't have type annotations anymore, they have been
 * transformed into type annotations onto the corresponding expression, i.e.
 * [EConstraint] nodes. *)
type pattern =
    PVar of Variable.name * location
  | PTuple of pattern list
  | PConstruct of resolved_datacon *
      (Field.name * pattern) list
  | POpen of var
  | PAs of pattern * pattern
  | PAny

type rec_flag = SurfaceSyntax.rec_flag = Nonrecursive | Recursive

(** This is not very different from {!SurfaceSyntax.expression}. Some nodes such
 * as [ESequence] have been removed. *)
type expression =
    EConstraint of expression * typ
  | EVar of db_index
  | EOpen of var
  | EBuiltin of string
  | ELet of rec_flag * patexpr list * expression
  | EFun of (type_binding * flavor) list * typ * typ * expression
  | EAssign of expression * field * expression
  | EAssignTag of expression * resolved_datacon * tag_update_info
  | EAccess of expression * field
  | EApply of expression * expression
  | ETApply of expression * tapp * kind
  | EMatch of bool * expression * patexpr list
  | ETuple of expression list
  | EConstruct of resolved_datacon * (Field.name * expression) list
  | EIfThenElse of bool * expression * expression * expression
  | ELocated of expression * location
  | EInt of int
  | EExplained of expression
  | EGive of expression * expression
  | ETake of expression * expression
  | EOwns of expression * expression
  | EFail

and tapp = Ordered of typ | Named of Variable.name * typ

and patexpr = pattern * expression

type declaration =
    DMultiple of rec_flag * patexpr list
  | DLocated of declaration * location

type sig_item = Variable.name * typ

type toplevel_item =
    DataTypeGroup of data_type_group
  | ValueDefinitions of declaration
  | ValueDeclaration of sig_item

type implementation = toplevel_item list

type interface = toplevel_item list


(* -------------------------------------------------------------------------- *)

(** {1 Substitution functions} *)

(** Of course, we have many more substitution functions, since now all the
 * substitution functions for types have to be extended to expressions and
 * patterns. The naming convention is as follows:
 * - [tsubst_X] substitutes a type for an index in an [X]
 * - [esubst_X] substitutes an expression for an index in an [X]
 * - [tpsubst_X] substitutes a var for a type in an [X]
 * - [epsubst_X] substitutes a var for an expression an [X]
 *
 * Because most of the things are done through the "substitution kit" (see
 * below), most of the variants for substitution functions are *not* exposed to
 * the client code.
 *)


(** {2 Convenience helpers} *)

(** The [()] (unit) expression. *)
val e_unit : expression

(** The [()] (unit) pattern. *)
val p_unit : pattern

(** Remove any [ELocated] node in front of an expression. *)
val eunloc : expression -> expression


(** {2 Substitution functions for types.} *)

val tsubst_toplevel_items :
  typ ->
  db_index -> toplevel_item list -> toplevel_item list

val tpsubst_expr :
  env -> typ -> var -> expression -> expression


(** {2 Substitution functions for expressions.} *)

val esubst_toplevel_items :
  expression -> db_index -> toplevel_item list -> toplevel_item list

val epsubst :
  env -> expression -> var -> expression -> expression


(* -------------------------------------------------------------------------- *)

(** {1 Binding functions} *)

(** To tame the combinatorial explosion, the binding functions in this module
 * return a substitution kit. That is to say, once you've bound type vars or
 * term vars, you're given a set of functions that you can apply on whatever you
 * need to open the binders. You are also given the list of (open) variables. *)
type substitution_kit = {
  subst_type : typ -> typ;
  subst_expr : expression -> expression;
  subst_decl : declaration -> declaration;
  subst_pat : pattern list -> pattern list;
  vars : var list;
}

(** Bind a set of term variables (let-bindings). *)
val bind_evars :
  env ->
  type_binding list -> env * substitution_kit

(** Bind a set of type variables (Λ-bindings). *)
val bind_vars :
  env ->
  SurfaceSyntax.type_binding list -> env * substitution_kit

(** Bind a set of multiple bindings ([and] keyword). The bindings may be
 * mutually recursive. There is also a set of expressions on the right-hand-side
 * of each [=] sign. The variables will also be opened there, and this function
 * takes care of doing it properly depending on whether these are recursive
 * bindings or not. 
 *
 * It is then up to the client code to open these variables in the body of the
 * multiple bindings. Consider for instance "let rec x = e1 and y = e2 in e"; this
 * function will correctly open "x" and "y" in "e1" and "e2" but you must use the
 * substitution kit to open "x" and "y" in "e". *)
val bind_patexprs :
  env ->
  rec_flag ->
  (pattern * expression) list ->
  env * (pattern * expression) list * substitution_kit

(** Our not-so-pretty printer for expressions. *)
module ExprPrinter :
  sig
    val print_maybe_qualified_datacon :
      Datacon.name SurfaceSyntax.maybe_qualified -> MzPprint.document
    val pmaybe_qualified_datacon :
      Buffer.t -> Datacon.name SurfaceSyntax.maybe_qualified -> unit
    val print_datacon_reference :
      SurfaceSyntax.datacon_reference -> MzPprint.document
    val print_patexpr :
      env -> pattern * expression -> MzPprint.document
    val print_patexprs :
      env -> (pattern * expression) list -> MzPprint.document
    val print_pat : env -> pattern -> MzPprint.document
    val print_tapp : env -> tapp -> MzPprint.document
    val print_expr : env -> expression -> MzPprint.document
    val print_rec_flag : rec_flag -> MzPprint.document
    val print_ebinder :
      env ->
      type_binding * flavor -> MzPprint.document
    val print_binder :
      env ->
      (Variable.name * kind * location) * flavor ->
      MzPprint.document
    val print_declaration :
      env ->
      declaration ->
      MzPprint.document
    val print_sig_item :
      env -> Variable.name * typ -> MzPprint.document
    val psigitem :
      Buffer.t -> env * (Variable.name * typ) -> unit
    val pdeclarations : Buffer.t -> env * declaration -> unit
    val pexpr : Buffer.t -> env * expression -> unit
    val ppat : Buffer.t -> env * pattern -> unit
  end
