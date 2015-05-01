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

(* This file contains our internal syntax for expressions. *)

open Kind
open TypeCore

(* ---------------------------------------------------------------------------- *)

(* Definitions borrowed from SurfaceSyntax. *)

type tag_update_info =
    SurfaceSyntax.tag_update_info

type field =
    SurfaceSyntax.field


(* ---------------------------------------------------------------------------- *)

(* Patterns *)

(* The De Bruijn numbering is defined according to a depth-first, left-to-right
 * traversal of the pattern: the first variable encountered will have index 0,
 * and so on. *)
type pattern =
  (* x *)
  | PVar of Variable.name * location
        (* TEMPORARY is the name important here, or just a hint? *)
  (* (x₁, …, xₙ) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of resolved_datacon * (Field.name * pattern) list
  (* Once the variables in a pattern have been bound, they may be replaced by
   * [POpen]s so that we know how to speak about the bound variables. *)
  | POpen of var
  | PAs of pattern * pattern
  | PAny


(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = SurfaceSyntax.rec_flag = Nonrecursive | Recursive

type expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v, bound *)
  | EVar of db_index
  (* v, free *)
  | EOpen of var
  (* builtin foo *)
  | EBuiltin of string
  (* let rec pat = expr and pat' = expr' in expr *)
  | ELet of rec_flag * patexpr list * expression
  (* let flex v in e *)
  | ELetFlex of (type_binding * flavor) * expression
  (* let alias t = τ in e *)
  | ELocalType of data_type_group * expression
  (* [a, ..., a] e *)
  | EBigLambdas of (type_binding * flavor) list * expression
  (* lambda (x: τ): τ -> e *)
  (* A lambda binds exactly one variable, which has de Bruijn index 0.
     The scope of this variable is the function body, [e].
     This is in contrast with the surface syntax, where many variables
     can be bound, and the argument type is interpreted as a pattern. *)
  | ELambda of typ * typ * expression
  (* v.f <- e *)
  | EAssign of expression * field * expression
  (* tag of v <- Foo *)
  | EAssignTag of expression * resolved_datacon * tag_update_info
  (* v.f *)
  | EAccess of expression * field
  (* assert τ *)
  | EAssert of typ
  (* pack {t} p witness t' *)
  | EPack of typ * typ
  (* e₁ e₂ *)
  | EApply of expression * expression
  (* e [τ₁, …, τₙ] *)
  | ETApply of expression * tapp * kind
  (* match e with pᵢ -> eᵢ *)
  | EMatch of bool * expression * patexpr list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of resolved_datacon * (Field.name * expression) list
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of bool * expression * expression * expression
  | ELocated of expression * location
  | EInt of int
  (* Adoption/abandon *)
  | EGive of expression * expression
  | ETake of expression * expression
  | EOwns of expression * expression
  (* fail *)
  | EFail

and tapp =
  | Ordered of typ
  | Named of Variable.name * typ

and patexpr =
  (* A binding is made up of a pattern, an optional type annotation for the
   * entire pattern (desugared), and an expression. *)
  pattern * expression

(* The grammar below doesn't enforce the “only variables are allowed on the
 * left-hand side of a let rec” rule. We'll see to that later. Here too, the
 * order of the bindings is significant: if the binding is recursive, the
 * variables in all the patterns are collected in order before type-checking the
 * expressions. *)

type definitions =
  location * rec_flag * (pattern * expression) list

type sig_item =
  Variable.name * typ

type toplevel_item =
  | DataTypeGroup of data_type_group
  | ValueDefinitions of definitions
  | ValueDeclaration of sig_item

type implementation =
  toplevel_item list

type interface =
  toplevel_item list

let internal_ppat: (Buffer.t -> (env * pattern) -> unit) ref = ref (fun _ _ -> assert false);;
let internal_ptapp: (Buffer.t -> (env * tapp) -> unit) ref = ref (fun _ _ -> assert false);;
