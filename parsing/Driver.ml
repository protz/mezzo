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

open Lexer

let include_dirs: string list ref =
  ref []
;;

let add_include_dir dir =
  include_dirs := dir :: !include_dirs
;;

let lex_and_parse file_path entry_point =
  let file_desc = open_in file_path in
  let lexbuf = Ulexing.from_utf8_channel file_desc in
  let parser = MenhirLib.Convert.Simplified.traditional2revised entry_point in
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

let check_implementation program = 
  let open Expressions in

  (* First pass of kind-checking; it checks for unbound variables and variables
   * with the wrong kind. *)
  KindCheck.check_implementation program;

  (* We need to translate the program down to the internal syntax. *)
  let program = TransSurface.translate_implementation program in

  let rec type_check env program =
    match program with
    | DataTypeGroup group :: blocks ->
        Log.debug ~level:2 "\n%s***%s Processing data type group:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          KindCheck.KindPrinter.pgroup (env, group);

        (* The binders in the data type group will be opened in the rest of the
         * blocks. Also performs the actual binding in the data type group, as
         * well as the variance and fact inference. *)
        let env, blocks = DataTypeGroup.bind_data_type_group env group blocks in
        (* Move on to the rest of the blocks. *)
        type_check env blocks
    | ValueDeclarations decls :: blocks ->
        Log.debug ~level:2 "\n%s***%s Processing declarations:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          Expressions.ExprPrinter.pdeclarations (env, decls);

        (* Perform the actual checking. The binders in the declaration group
         * will be opened in [blocks] as well. *)
        let env, blocks = TypeChecker.check_declaration_group env decls blocks in
        (* Move on to the rest of the blocks. *)
        type_check env blocks
    | [] ->
        (* Print some extra debugging information. *)
        Log.debug ~level:2 "\n%s***%s Done type-checking:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          Types.TypePrinter.pdoc
          (KindCheck.KindPrinter.print_kinds_and_facts, env);

        (* Do the final checks (is this the right time?) *)
        ExtraChecks.check_env env;
        env
  in

  (* Let's do it! *)
  type_check Types.empty_env program
;;

let check_interface env iface =
  ignore (env, iface);
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

(* [find_interface mz] returns the path to the interface for [mz], if any. It
 * assumes [mz] is a valid filename ending with ".mz". *)
let find_interface file_path =
  let iface = file_path ^ "i" in
  if Sys.file_exists iface then
    Some iface
  else
    None
;;

let process use_pervasives file_path =
  if not (Filename.check_suffix file_path ".mz") then
    Log.error "Bad filename: Mezzo files end with .mz";
  if not (Sys.file_exists file_path) then
    Log.error "File %s does not exist" file_path;

  let program =
    let prefix = 
      (* HACK HACK HACK *)
      if use_pervasives then
        let path_to_pervasives = find_in_include_dirs "pervasives.mz" in
        lex_and_parse path_to_pervasives Grammar.implementation
      else
        []
    in
    prefix @ lex_and_parse file_path Grammar.implementation
  in

  let env = check_implementation program in

  match find_interface file_path with
  | Some iface_path ->
      let interface = lex_and_parse iface_path Grammar.interface in
      check_interface env interface;
      env
  | None ->
      env
;;

type run_options = {
  html_errors: bool;
}

let run { html_errors } f =
  try
    f ()
  with
  | TypeErrors.TypeCheckerError ((env, _) as e) ->
      if html_errors then begin
        (* Get a plain-text version of the error *)
        Hml_Pprint.disable_colors ();
        let text = Hml_String.bsprintf "%a\n" TypeErrors.print_error e in
        (* Generate the HTML explanation. *)
        Debug.explain ~text env;
        (* Find out about the command to run. *)
        let f = (fst env.Types.location).Lexing.pos_fname in
        let f = Hml_String.replace "/" "_" f in
        let cmd = Printf.sprintf
          "firefox -new-window \"viewer/viewer.html?json_file=data/%s.json\" &"
          f
        in
        (* Let's do it! *)
        ignore (Sys.command cmd)
      end else begin
        Hml_String.beprintf "%a\n" TypeErrors.print_error e;
      end;
      exit 251
  | KindCheck.KindError e ->
      Hml_String.beprintf "%a\n" KindCheck.print_error e;
      exit 250
;;

let print_signature (buf: Buffer.t) (env: Types.env): unit =
  flush stdout;
  flush stderr;
  let open Types in
  let compare_locs loc1 loc2 =
    Lexing.(compare loc1.pos_cnum loc2.pos_cnum)
  in
  let perms = fold_terms env (fun acc point { locations; _ } { permissions; _ } ->
    let locations = List.sort (fun (loc1, _) (loc2, _) -> compare_locs loc1 loc2) locations in
    let location = fst (List.hd locations) in
    List.map (fun x -> point, location, x) permissions :: acc
  ) [] in
  let perms = List.flatten perms in
  let perms = List.filter (fun (point, _, perm) ->
    match perm with
    | TyUnknown ->
        false
    | TySingleton (TyPoint point') when same env point point' ->
        false
    | _ ->
        true
  ) perms in
  let perms = List.sort (fun (_, loc1, _) (_, loc2, _) -> compare_locs loc1 loc2) perms in
  List.iter (fun (point, _, perm) ->
    let open TypePrinter in
    let open Hml_Pprint in
    pdoc buf ((fun () ->
      let t = print_type env perm in
      print_names (get_names env point) ^^ space ^^ at ^^ space ^^ (nest 2 t) ^^
      break1
    ), ())
  ) perms
;;
