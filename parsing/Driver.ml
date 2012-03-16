(*****************************************************************************)
(*  HaMLet, a ML dialect with a type-and-capability system                   *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
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

open Lexer

let include_dirs: string list ref =
  ref []
;;

let add_include_dir dir =
  include_dirs := dir :: !include_dirs
;;

type substitution = Expressions.declaration_group -> Expressions.declaration_group

type state = {
  type_env: Types.env;
  kind_env: WellKindedness.env;
  subst: substitution;
}

let empty_state = {
  type_env = Types.empty_env;
  kind_env = WellKindedness.empty;
  subst = fun x -> x;
}

let lex_and_parse file_path =
  let file_desc = open_in file_path in
  let lexbuf = Ulexing.from_utf8_channel file_desc in
  let parser = MenhirLib.Convert.Simplified.traditional2revised Grammar.unit in
  try
    Lexer.init file_path;
    parser (fun _ -> Lexer.token lexbuf)
  with 
    | Ulexing.Error -> 
	Printf.eprintf 
          "Lexing error at offset %i\n" (Ulexing.lexeme_end lexbuf);
        exit 255
    | Ulexing.InvalidCodepoint i -> 
	Printf.eprintf 
          "Invalid code point %i at offset %i\n" i (Ulexing.lexeme_end lexbuf);
        exit 254
    | Grammar.Error ->
        Hml_String.beprintf "%a\nError: Syntax error\n"
          print_position lexbuf;
        exit 253
    | Lexer.LexingError e ->
        Hml_String.beprintf "%a\n"
          Lexer.print_error (lexbuf, e);
        exit 252
;;

let type_check program = 
  let type_env, declarations = WellKindedness.check_program Types.empty_env program in
  let type_env = FactInference.analyze_data_types type_env in
  Log.debug ~level:2 "%a"
    Types.TypePrinter.pdoc
    (WellKindedness.KindPrinter.print_kinds_and_facts, type_env);
  Log.debug ~level:2 "%a"
    Types.TypePrinter.pdoc
    (Expressions.ExprPrinter.pdeclarations, (type_env, declarations));
  let type_env = TypeChecker.check_declaration_group type_env declarations in
  type_env
;;

let find_in_include_dirs (filename: string): string =
  let module M = struct exception Found of string end in
  try
    List.iter (fun dir ->
      let open Filename in
      let dir =
        if is_relative dir then
          current_dir_name ^ dir_sep ^ dir
        else
          dir
      in
      let path = concat dir filename in
      Log.debug "Trying %s" path;
      if Sys.file_exists path then
        raise (M.Found path)
    ) !include_dirs;
    Log.error "File %s not found in any include directory." filename
  with M.Found s ->
    s
;;

let process file_path =
  let path_to_pervasives = find_in_include_dirs "pervasives.hml" in
  let defs, declarations = lex_and_parse path_to_pervasives in
  let defs', declarations' = lex_and_parse file_path in
  (* HACK HACK HACK *)
  let program = defs @ defs', declarations @ declarations' in
  type_check program
;;

let run f =
  let open TypeChecker in
  try
    f ()
  with
  | TypeCheckerError e ->
      Hml_String.beprintf "%a\n" print_error e;
      exit 251
;;
