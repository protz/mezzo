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

(** This module defines substitution functions and binding functions on
 * expressions as well as data type groups. *)

open Kind
open TypeCore
open ExpressionsCore


(* -------------------------------------------------------------------------- *)

(** {1 Data type groups} *)

(** This function processes a {!data_type_group}, and opens the corresponding
 * binders in the {!toplevel_item}s that follow. The resulting {!toplevel_item}s
 * are returned, as well as the list of {!var}s that have been bound. *)
val bind_data_type_group_in_toplevel_items: env -> data_type_group -> toplevel_item list ->
      env * toplevel_item list * var list

(** Used by the type-checker to process local type declarations. *)
val bind_data_type_group_in_expr: env -> data_type_group -> expression ->
      env * expression * var list

(** Use this to transform the branch from a [type_def] into something that's
 * suitable for manipulation as a type. *)
val resolve_branch: var -> branch -> branch

(* TEMPORARY this whole thing seems to duplicate [KindCheck] *)


(* -------------------------------------------------------------------------- *)

(** {1 Substitution functions} *)

(** Of course, we have many more substitution functions, since now all the
 * substitution functions for types have to be extended to expressions and
 * patterns. The naming convention is as follows:
 * - [tsubst_X] substitutes a type for an index in an [X]
 * - [esubst_X] substitutes an expression for an index in an [X]
 * - [tpsubst_X] substitutes a var for a type in an [X]
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


(** {2 Substitution functions for expressions.} *)

val tsubst_expr: typ -> int -> expression -> expression

val esubst_toplevel_items :
  expression -> db_index -> toplevel_item list -> toplevel_item list


(* -------------------------------------------------------------------------- *)

(** {1 Binding functions} *)

(** To tame the combinatorial explosion, the binding functions in this module
 * return a substitution kit. That is to say, once you've bound type vars or
 * term vars, you're given a set of functions that you can apply on whatever you
 * need to open the binders. You are also given the list of (open) variables. *)
type substitution_kit = {
  subst_type : typ -> typ;
  subst_expr : expression -> expression;
  subst_def : definitions -> definitions;
  subst_toplevel: toplevel_item list -> toplevel_item list;
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
    val print_definitions:
      env ->
      definitions ->
      MzPprint.document
    val print_sig_item :
      env -> Variable.name * typ -> MzPprint.document
    val psigitem :
      Buffer.t -> env * (Variable.name * typ) -> unit
    val pdefinitions : Buffer.t -> env * definitions -> unit
    val pexpr : Buffer.t -> env * expression -> unit
    val ppat : Buffer.t -> env * pattern -> unit
  end
