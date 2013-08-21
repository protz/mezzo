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

(** Handling the names exported by interfaces and implementations. *)

(** From a very high-level perspective, the type-checker needs to maintain a map
 * from names to [TypeCore.var]s.
 *   - We need to map _qualified_ names to [var]s (What is the [var] that stands
 *   for "int::int"?), and
 *   - we need to map _unqualified_ names to [var]s (This implementation
 *   contains "val x". Which [var] is "x"?)
 *
 * Qualified names are added to this map when importing an interface.
 * Unqualified names are added when type-checking an implementation.
 *
 * What does this have to do with kind-check? Well, kind-check expects an
 * environment where all required interfaces have been _imported_. This means
 * that if there is an occurrence of module "m" in implementation "impl", then
 * kind-checking expects "m::x" to be available in the environment. Opening a
 * module is managed internally by [KindCheck] and [TransSurface].
 *
 * Rather than using a separate, high-level environment, which we would inject
 * into the kind-checking environment, we cheat and reuse kind-checking
 * environments as high-level environments. The invariant is that a high-level
 * environment only contains [NonLocal] bindings, either qualified or
 * unqualified. *)


(** This is the type of a high-level environment. *)
type env = TypeCore.var KindCheck.env

type value_exports = (Variable.name * TypeCore.var) list
type datacon_exports = (TypeCore.var * Datacon.name * SurfaceSyntax.datacon_info) list

val bind_implementation_values:
  TypeCore.env -> value_exports ->
    TypeCore.env
val bind_implementation_types:
  TypeCore.env -> TypeCore.data_type_group -> TypeCore.var list -> datacon_exports ->
    TypeCore.env
val bind_interface_value:
  TypeCore.env -> Module.name -> Variable.name -> TypeCore.var ->
    TypeCore.env
val bind_interface_types:
  TypeCore.env -> Module.name -> TypeCore.data_type_group -> TypeCore.var list -> datacon_exports ->
    TypeCore.env
