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

(* let e = Mezzo2UntypedMezzo.translate_implementation (* TEMPORARY *)
let f = UntypedMezzo2UntypedOCaml.translate_implementation (* TEMPORARY *) *)

type mode =
  | TypecheckAndCompile
  | Interpret

let _ =
  let arg_debug = ref 0 in
  let arg_backtraces = ref true in
  let arg_trace = ref "" in
  let arg_html_errors = ref false in
  let arg_mode = ref TypecheckAndCompile in
  let usage = "Mezzo: a next-generation version of ML\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-explain", Arg.Set_string arg_trace, "<format>  The explain keyword \
      generates a graphical dump, where <format> is one of html, x11";
    "-nofancypants", Arg.Clear arg_backtraces, " Don't catch type errors: \
      backtraces point to the place where the error was thrown";
    "-debug", Arg.Set_int arg_debug, " <level>  Output level: 0 (default) = no \
      messages, 5 = super super verbose";
    "-html-errors", Arg.Unit (fun () ->
        arg_html_errors := true;
        arg_trace := "html"), " Use a browser to display errors";
    "-pedantic", Arg.Set Options.pedantic, " Non-principal situations are errors";
    "-I", Arg.String Driver.add_include_dir, " <dir>  Add <dir> to the list of \
      include directories";
    "-noautoinclude", Arg.Set Options.no_auto_include, "  Don't automatically \
      open the corelib modules";
    "-nosigcheck", Arg.Set Options.no_sig_check, "  [for debugging only, unsound]";
    "-c", Arg.Unit (fun () -> arg_mode := TypecheckAndCompile), "type-check and compile (default)";
    "-i", Arg.Unit (fun () -> arg_mode := Interpret), "do not type-check; interpret";
  ] (fun f ->
    if !Options.filename = "" then
      Options.filename := f
    else
      failwith "Only one filename should be specified.\n"
  ) usage;
  if !Options.filename = "" then begin
    print_string usage;
    exit 1;
  end;
  Log.enable_debug !arg_debug;
  Debug.enable_trace !arg_trace;
  let opts =
    let open Driver in
    { html_errors = !arg_html_errors }
  in
  Driver.add_include_dir (Filename.concat Configure.root_dir "corelib");
  Driver.add_include_dir (Filename.concat Configure.root_dir "stdlib");
  Driver.add_include_dir (Filename.dirname !Options.filename);
  match !arg_mode with
  | TypecheckAndCompile ->
      let env =
	if !arg_backtraces then
	  Driver.run opts (fun () -> Driver.process !Options.filename)
	else
	  Driver.process !Options.filename
      in
      if Log.debug_level () <= 0 then
	Hml_String.bprintf "%a" Driver.print_signature env
      else
	Log.debug ~level:0 "\n%a"
	  Types.TypePrinter.pdoc (Types.TypePrinter.print_permissions, env)
  | Interpret ->
      Driver.interpret !Options.filename
;;
