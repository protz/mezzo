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

type rec_flag =
    SurfaceSyntax.rec_flag

type expression =
    (* Unqualified and qualified references are conflated. *)
  | EVar of string
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
    (* Generic field and tag manipulation operations. *)
  | ESetField of expression * int * expression
  | ESetTag of expression * int
  | EGetField of expression * int
  | EGetTag of expression
    (* Type casts. *)
  | EMagic of expression
  | ERepr of expression

(* ---------------------------------------------------------------------------- *)

(* Top-level declarations *)

(* TEMPORARY *)

