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

open Kind

type var
type env
type raw_error
type error = env * raw_error
exception KindError of error

(* TEMPORARY try not to publish any of the functions that raise errors *)
val field_mismatch: env -> Datacon.name -> SurfaceSyntax.Field.name list (* missing fields *) -> SurfaceSyntax.Field.name list (* extra fields *) -> 'a
val implication_only_on_arrow: env -> 'a
val illegal_consumes: env -> 'a
val print_error: Buffer.t -> error -> unit


val empty: TypeCore.env -> env
val bind: env -> Variable.name * kind -> env
val bind_external: env -> Variable.name * kind * TypeCore.var -> env
val bind_datacons: env -> SurfaceSyntax.data_type_def list -> env
val open_module_in: Module.name -> env -> env
val locate: env -> Lexing.position * Lexing.position -> env

val location: env -> Lexing.position * Lexing.position
val module_name: env -> Module.name
val find_var: Variable.name SurfaceSyntax.maybe_qualified -> env -> var
val find_datacon: Datacon.name SurfaceSyntax.maybe_qualified -> env -> SurfaceSyntax.datacon_info * TypeCore.resolved_datacon


val tvar: var -> env -> TypeCore.typ
val evar: var -> env -> Expressions.expression

val names: env -> SurfaceSyntax.typ -> SurfaceSyntax.type_binding list
val bindings_pattern: SurfaceSyntax.pattern -> (Variable.name * kind) list
val bindings_patterns: SurfaceSyntax.pattern list -> (Variable.name * kind) list

val bindings_data_type_group: SurfaceSyntax.data_type_def list -> (Variable.name * kind) list

val check_type_with_names: env -> SurfaceSyntax.typ -> kind -> unit
val infer_type_with_names: env -> SurfaceSyntax.typ -> kind

val check_implementation: TypeCore.env -> SurfaceSyntax.implementation -> unit
val check_interface: TypeCore.env -> SurfaceSyntax.interface -> unit

module KindPrinter : sig
  val pgroup: Buffer.t -> TypeCore.env * TypeCore.data_type_group -> unit
  val print_kinds_and_facts: TypeCore.env -> MzPprint.document
end
