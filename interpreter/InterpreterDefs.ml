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

(* These are the definitions of values and environments for the Mezzo
   interpreter. *)

open SurfaceSyntax

(* ---------------------------------------------------------------------------- *)

(* The interpreter treats data constructor definitions as generative. That is,
   the evaluation of a data constructor definition causes the generation of a
   fresh (integer) identifier, to which the data constructor becomes bound.
   Data constructors are treated just like variables (i.e., they are bound in
   the environment. (This implies, for instance, that if a function refers to a
   data constructor, then this data constructor is interpreted in the closure's
   environment.) We adopt this approach because it seems simple, efficient, and
   deals correctly with masking. *)

type datacon_id =
    int

(* We maintain the following information about every data constructor. *)

type datacon_info = {
  (* Its unique identifier. *)
  datacon_id: datacon_id;
  (* Its arity (i.e., number of fields). *)
  datacon_arity: int;
  (* Its integer index within its data type definition. *)
  datacon_index: int;
  (* A map of field names to field indices. *)
  datacon_fields: int Variable.Map.t;
}

(* ---------------------------------------------------------------------------- *)

(* Thus, we have two namespaces: variables and data constructors. *)

module V =
  InterpreterNamespace.MakeNamespace(Variable)

module D =
  InterpreterNamespace.MakeNamespace(Datacon)

(* ---------------------------------------------------------------------------- *)

(* An environment contains the following information: *)

type env = {
    (* A map of (unqualified or qualified) variables to values. *)
    variables: value V.global_env;
    (* A map of (unqualified) data constructors to identifiers. *)
    datacons: datacon_id D.global_env;
    (* The number of the next available unique data constructor identifier. *)
    next_datacon_id: datacon_id;
}

(* ---------------------------------------------------------------------------- *)

(* A value is one of the following: *)

and value =
    (* A primitive integer value. *)
  | VInt of int
    (* The address of a memory block. *)
  | VAddress of block
    (* A tuple. *)
  | VTuple of value list
    (* A closure. *)
  | VClosure of closure

(* A memory block contains the following information: *)

and block = {
  (* A tag. *)
  mutable tag: datacon_id;
  (* An adopter pointer, which is either null or the address of some other block. *)
  mutable adopter: block option;
  (* A set of fields. *)
  fields: value (* mutable *) array;
}

(* A closure contains the following information: *)

and closure = {
  (* The function's formal argument, a pattern. *)
  arg: pattern;
  (* The function's body, an expression. *)
  body: expression;
  (* The environment. *)
  (* This field is mutable only in order to allow initializing
     a recursive closure (this is Landin's knot). *)
  mutable env: env;
}
