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

(* This is the definition of Untyped OCaml. *)

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

type pattern =
  | PVar of string
  | PTuple of pattern list
    (* Data constructor pattern. *)
  | PConstruct of string * pattern list
    (* Record pattern. *)
  | PRecord of (string * pattern) list
  | PAs of pattern * string
  | PAny

(* ---------------------------------------------------------------------------- *)

(* Expressions. *)

type rec_flag =
    SurfaceSyntax.rec_flag

type expression =
    (* Unqualified and qualified references are conflated. *)
  | EVar of string
  | EInfixVar of string (* e.g., ">" *)
  | ELet of rec_flag * (pattern * expression) list * expression
  | EFun of pattern * expression
    (* Record field access. *)
  | EAssign of expression * string * expression
  | EAccess of expression * string
  | EApply of expression * expression
  | EMatch of expression * (pattern * expression) list
  | ETuple of expression list
    (* Data constructor expression. *)
  | EConstruct of string * expression list
    (* Record expression. *)
  | ERecord of (string * expression) list
  | EIfThenElse of expression * expression * expression
  | ESequence of expression * expression
  | EInt of int
  | EStringLiteral of string
    (* Generic field and tag manipulation operations. *)
  | ESetField of expression * int * expression
  | ESetTag of expression * int
  | EGetField of expression * int
  | EGetTag of expression
    (* Type casts. *)
  | EMagic of expression
  | ERepr of expression

(* ---------------------------------------------------------------------------- *)

(* Types. *)

type ty =
  | TyBound of string (* quote included *)

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_branch =
    (* data constructor name, argument types *)
    string * ty list
      
type data_type_def_lhs =
    (* type name, type parameters *)
    string * string list

type mutability =
  | Immutable
  | Mutable

type record_def =
    (* field names and types *)
    (mutability * string * ty) list

type data_type_def_rhs =
  | Sum of data_type_def_branch list
  | Record of record_def

type data_type_def =
    data_type_def_lhs * data_type_def_rhs

(* ---------------------------------------------------------------------------- *)

(* Value definitions. *)

type definition =
    rec_flag * (pattern * expression) list

(* ---------------------------------------------------------------------------- *)

(* Top-level items. *)

type toplevel_item =
  | DataTypeGroup of data_type_def
  | ValueDefinition of definition
  | ValueDeclaration of string * ty
  | OpenDirective of string

type implementation =
    toplevel_item list

type interface =
    toplevel_item list

