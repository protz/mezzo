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

(* This module provides the definitions of values and environments. *)

open SurfaceSyntax

(* ---------------------------------------------------------------------------- *)

(* Toplevel variables and data constructors are qualified with a module name.
   Local variables are not qualified. We encode them as variables qualified
   with a dummy module name. *)

let local : Module.name =
  Module.register "<local>"

module Qualify (X : sig
  type name
  val compare : name -> name -> int
end) = struct
  type name = Module.name * X.name
  type t = name
  let compare (m1, x1) (m2, x2) =
    let c = X.compare x1 x2 in
    if c <> 0 then c
    else Module.compare m1 m2
end

module QualifiedVariable = Qualify(Variable)
module QualifiedVariableMap = Hml_Map.Make(QualifiedVariable)

module QualifiedDatacon = Qualify(Datacon)
module QualifiedDataconMap = Hml_Map.Make(QualifiedDatacon)

(* ---------------------------------------------------------------------------- *)

(* An environment maps qualified variables to values. *)

type env =
    value QualifiedVariableMap.t

(* ---------------------------------------------------------------------------- *)

(* A value is one of the following: *)

and value =
    (* A primitive integer value. *)
  | VInt of int
    (* The address of a memory block. *)
  | VAddress of block
    (* A tuple. *)
  | VTuple of value (* immutable *) array
    (* A closure. *)
  | VClosure of closure

(* A memory block contains the following information: *)

and block = {
  (* A tag. *)
  mutable tag: QualifiedDatacon.name;
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
  env: env;
}
