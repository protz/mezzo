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

(** This module defines the syntax of expressions. *)

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
  | PConstruct of resolved_datacon * (Field.name * pattern) list
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
  | ELetFlex of (type_binding * flavor) * expression
  | ELocalType of data_type_group * expression
  | EBigLambdas of (type_binding * flavor) list * expression
  | ELambda of typ * typ * expression
  | EAssign of expression * field * expression
  | EAssignTag of expression * resolved_datacon * tag_update_info
  | EAccess of expression * field
  | EAssert of typ
  | EPack of typ * typ
  | EApply of expression * expression
  | ETApply of expression * tapp * kind
  | EMatch of bool * expression * patexpr list
  | ETuple of expression list
  | EConstruct of resolved_datacon * (Field.name * expression) list
  | EIfThenElse of bool * expression * expression * expression
  | ELocated of expression * location
  | EInt of int
  | EGive of expression * expression
  | ETake of expression * expression
  | EOwns of expression * expression
  | EFail

and tapp = Ordered of typ | Named of Variable.name * typ

and patexpr = pattern * expression

type definitions =
  location * rec_flag * (pattern * expression) list

type sig_item = Variable.name * typ

type toplevel_item =
    DataTypeGroup of data_type_group
  | ValueDefinitions of definitions
  | ValueDeclaration of sig_item

type implementation = toplevel_item list

type interface = toplevel_item list

(**/**)

val internal_ppat: (Buffer.t -> (env * pattern) -> unit) ref
val internal_ptapp: (Buffer.t -> (env * tapp) -> unit) ref
