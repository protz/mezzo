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

(** Treatment of interfaces. *)

(** The first operation related to interfaces consists in importing a given
 * interface into an environment. This can be achieved by calling
 * [import_interface env mname iface], which will import the surface syntax
 * interface [iface], belonging to module [mname], into [env]. Obtaining the
 * surface syntax interface is the job of the driver.
 *
 * This will perform several tasks. First, value definitions and data type
 * definitions will be bound in [env]. Second, the inner kind-checking
 * environment of [env] will be extended with bindings of the form "mname::x" to
 * stand for the variables "x" exported by module "mname". *)
val import_interface : TypeCore.env -> Module.name -> SurfaceSyntax.interface -> TypeCore.env

(** The second operation related to interfaces consists in checking that an
 * implementation satisfies a given interface. For that purpose, one can cell
 * [check env iface]. We expect [env] to be in a specific form, which is
 * attained by [Driver] after a call to [type_check]: the kinding environment of
 * [env] must contain non-local, non-qualified names that represent the names
 * exported by the implementation. *)
val check:
  TypeCore.env ->
  SurfaceSyntax.interface ->
  TypeCore.env
