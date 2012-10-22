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

let _ =
  let arg_filename = ref "" in
  let arg_debug = ref 0 in
  let arg_pervasives = ref true in
  let arg_backtraces = ref true in
  let arg_trace = ref "" in
  let arg_html_errors = ref false in
  let usage = "Mezzo: a next-generation version of ML\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-explain", Arg.Set_string arg_trace, "<format>  The explain keyword \
      generates a graphical dump, where <format> is one of html, x11";
    "-nopervasives", Arg.Clear arg_pervasives, " Don't try to prepend pervasives.mz to the file";
    "-nofancypants", Arg.Clear arg_backtraces, " Don't catch type errors: \
      backtraces point to the place where the error was thrown";
    "-debug", Arg.Set_int arg_debug, " <level>  Output level: 0 (default) = no \
      messages, 5 = super super verbose";
    "-html-errors", Arg.Set arg_html_errors, " Use a browser to display errors";
    "-pedantic", Arg.Set Options.pedantic, " Non-principal situations are errors";
    "-I <dir>", Arg.String Driver.add_include_dir, "  Add <dir> to the list of \
      include directories";
  ] (fun f ->
    if !arg_filename = "" then
      arg_filename := f
    else
      failwith "Only one filename should be specified.\n"
  ) usage;
  if !arg_filename = "" then begin
    print_string usage;
    exit 1;
  end;
  Log.enable_debug !arg_debug;
  Debug.enable_trace !arg_trace;
  let opts =
    let open Driver in
    { html_errors = !arg_html_errors }
  in
  Driver.add_include_dir (Filename.dirname !arg_filename);
  let env =
    if !arg_backtraces then
      Driver.run opts (fun () -> Driver.process !arg_pervasives !arg_filename)
    else
      Driver.process !arg_pervasives !arg_filename
  in
  if Log.debug_level () <= 0 then
    Hml_String.bprintf "%a" Driver.print_signature env
  else
    Log.debug ~level:0 "\n%a"
      Types.TypePrinter.pdoc (Types.TypePrinter.print_permissions, env);
;;
