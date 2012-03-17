(*****************************************************************************)
(*  HaMLet, a ML dialect with a type-and-capability system                   *)
(*  Copyright (C) 2011 Jonathan Protzenko                                    *)
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

(** This module sets up a lexer and a parser to create an AST. *)

type state = {
  type_env: Types.env;
  kind_env: WellKindedness.env;
  subst: substitution;
}

and substitution = Expressions.declaration_group -> Expressions.declaration_group

val empty_state: state

val add_include_dir: string -> unit
val find_in_include_dirs: string -> string

(** [lex_and_parse] is useful for tests that want to manipulate directly the
    AST. Otherwise, you should probably use [process]. *)
val lex_and_parse: string -> SurfaceSyntax.program

(** [type_check] is the next step after [lex_and_parse]. *)
val type_check: SurfaceSyntax.program -> Types.env

(** [process] doesn't catch exceptions. This is useful for tests that want to
    assert that a test program failed in a certain way. *)
val process: bool -> string -> Types.env

(** [run] runs the specified function and prints any error that may pop up. *)
val run: (unit -> 'a) -> 'a
