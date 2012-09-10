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
  KindCheck.check_program program;
  let type_env, declarations = TransSurface.translate Types.empty_env program in
  let type_env = FactInference.analyze_data_types type_env in
  let type_env = Variance.analyze_data_types type_env in
  Log.debug ~level:2 "%a"
    Types.TypePrinter.pdoc
    (KindCheck.KindPrinter.print_kinds_and_facts, type_env);
  Log.debug ~level:2 "%a"
    Expressions.ExprPrinter.pdeclarations (type_env, declarations);
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
      if Sys.file_exists path then
        raise (M.Found path)
    ) !include_dirs;
    Log.error "File %s not found in any include directory." filename
  with M.Found s ->
    s
;;

let process use_pervasives file_path =
  (* HACK HACK HACK *)
  let program =
    if use_pervasives then
      let path_to_pervasives = find_in_include_dirs "pervasives.hml" in
      let defs, declarations = lex_and_parse path_to_pervasives in
      let defs', declarations' = lex_and_parse file_path in
      defs @ defs', declarations @ declarations'
    else
      lex_and_parse file_path
  in
  type_check program
;;

type run_options = {
  html_errors: bool;
}

let run { html_errors } f =
  try
    f ()
  with
  | TypeChecker.TypeCheckerError ((env, _) as e) ->
      if html_errors then begin
        (* Get a plain-text version of the error *)
        Hml_Pprint.disable_colors ();
        let text = Hml_String.bsprintf "%a\n" TypeChecker.print_error e in
        (* Generate the HTML explanation. *)
        Debug.explain ~text env;
        (* Find out about the command to run. *)
        let f = (fst env.Types.location).Lexing.pos_fname in
        let f = Hml_String.replace "/" "_" f in
        let cmd = Printf.sprintf
          "firefox \"viewer/viewer.html?json_file=data/%s.json\" &"
          f
        in
        (* Let's do it! *)
        ignore (Sys.command cmd)
      end else begin
        Hml_String.beprintf "%a\n" TypeChecker.print_error e;
      end;
      exit 251
  | KindCheck.KindError e ->
      Hml_String.beprintf "%a\n" KindCheck.print_error e;
      exit 250
;;
