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

(** The lexer for Mezzo. *)

(** The abstract type of lexer errors. *)
type error

(** A lexer error can be thrown by the function [token]. *)
exception LexingError of error

(** [init filename] must be called before using the lexer. *)
val init: string -> unit

(** [token] is the main entry point of the lexer. It produces one
    token or raises [LexingError]. *)
val token: Ulexing.lexbuf -> Grammar.token * Lexing.position * Lexing.position

(** [print_error] displays a lexer error. *)
val print_error: Buffer.t -> (Ulexing.lexbuf * error) -> unit

(** [print_position] displays the lexer's current position. It can be used
    to build a syntax error message. *)
val print_position: Buffer.t -> Ulexing.lexbuf -> unit

(** [p] displays the position that is passed as an argument. It can be used
    to build (say) type error messages. *)
val p: Buffer.t -> Lexing.position * Lexing.position -> unit
