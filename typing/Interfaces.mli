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

(** Check a module against an interface / import an interface into scope. *)

(** Because this is a tricky operation, the [check] function needs access to
 * both the internal representation of the type-checked file (this is a
 * {!TypeCore.env}), the external representation of the interface (this is a
 * {!SurfaceSyntax.interface}), and the list of exported variables from the
 * implementation, along with their canonical names and kinds ({!Driver} knows
 * how to figure that out).
 *
 * This is not only about checking that a module satisfies its interface, but
 * also about checking that a module does not alter other interfaces. The
 * implementation has more comments along with the code. *)
val check:
  TypeCore.env ->
  SurfaceSyntax.interface ->
  (Variable.name * Kind.kind * TypeCore.var) list ->
    TypeCore.env

(** Import a given module into scope. *)
val import_interface : TypeCore.env -> Module.name -> SurfaceSyntax.interface -> TypeCore.env
