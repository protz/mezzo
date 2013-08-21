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

(** Translating the surface syntax down into the core language syntax. *)

open SurfaceSyntax

type env = TypeCore.var KindCheck.env

(** [translate_type_reset] translates a type. *)
val translate_type_reset: env -> typ -> TypeCore.typ

(** [translate_data_type_group extend env group] translates a data type group.
    The [extend] function is passed a (list of) pairs of a data type name and
    a kind, and must extend the environment in a suitable way (i.e., this name
    could be mapped to a fresh variable, or to an existing point; see
    [KindCheck]). The function returns a pair of an environment that has been
    extended with new types and new data constructors, and a translated data
    type group. *)
val translate_data_type_group:
  (env -> type_binding list -> env) ->
  env ->
  data_type_group ->
  env * TypeCore.data_type_group

(** [translate_implementation] translates a compilation unit. *)
val translate_implementation: env -> toplevel_item list -> ExpressionsCore.implementation

(** [translate_interface] translates an interface. *)
val translate_interface: env -> toplevel_item list -> ExpressionsCore.interface
