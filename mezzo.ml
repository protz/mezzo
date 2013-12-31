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

(** This is the entry point of the program. It parses command-line arguments,
 * sets up the {!Options} and calls in to {!Driver}. *)

type mode =
  | Typecheck
  | TypecheckAndCompile
  | Interpret

let _ =
  let arg_debug = ref 0 in
  let arg_backtraces = ref true in
  let arg_trace = ref "" in
  let arg_html_errors = ref false in
  let arg_mode = ref Typecheck in
  let arg_warn_error = ref "" in
  let arg_print_config = ref false in
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
    "-warn-error", Arg.Set_string arg_warn_error, " Decide which errors are fatal / warnings / silent. Same syntax as OCaml.";
    "-I", Arg.String Driver.add_include_dir, " <dir>  Add <dir> to the list of \
      include directories";
    "-noautoinclude", Arg.Set Options.no_auto_include, "  Don't automatically \
      open the corelib modules";
    "-boot", Arg.Set Options.boot, "  Used only when compiling the Mezzo \
      core and standard library";
    "-print-config", Arg.Set arg_print_config, "  Print Mezzo's configuration, e.g. include directories";
    "-c", Arg.Unit (fun () -> arg_mode := TypecheckAndCompile), "type-check and compile";
    "-i", Arg.Unit (fun () -> arg_mode := Interpret), "do not type-check; interpret";
    "-t", Arg.Unit (fun () -> arg_mode := Typecheck), "just type-check (default)";
  ] (fun f ->
    if !Options.filename = "" then
      Options.filename := f
    else
      failwith "Only one filename should be specified.\n"
  ) usage;
  (* Enable debugging and tracing. *)
  Log.enable_debug !arg_debug;
  Debug.enable_trace !arg_trace;

  (* First enable the default warn-error string. *)
  TypeErrors.parse_warn_error !Options.warn_error;

  (* Then refine that based on the user's preferences. *)
  if !arg_warn_error <> "" then
    TypeErrors.parse_warn_error !arg_warn_error;

  let opts =
    let open Driver in
    { html_errors = !arg_html_errors; backtraces = not !arg_backtraces }
  in

  (* In the local mode, corelib ana stdlib are to be found in the source
   * directory. If packaged, then everything's flat in the libdir. *)
  if !Options.boot || Configure.local then begin
    Driver.add_include_dir (Filename.concat Configure.src_dir "corelib");
    Driver.add_include_dir (Filename.concat Configure.src_dir "stdlib");
  end else begin
    Driver.add_include_dir Configure.lib_dir;
  end;
  Driver.add_include_dir (Filename.dirname !Options.filename);

  (* Print these parameters and exit, if that's what the user asked for. *)
  if !arg_print_config then begin
    Printf.printf "Booting:\n  %b\n" !Options.boot;
    Printf.printf "Local (developer's) build:\n  %b\n" Configure.local;
    Printf.printf "Configure.src_dir:\n  %s\n" Configure.src_dir;
    Printf.printf "Configure.lib_dir:\n  %s\n" Configure.lib_dir;
    Printf.printf "Include directories:\n  %s\n" (Driver.print_include_dirs ());
    exit 0;
  end;

  (* At this stage, we _do_ need a filename. *)
  if !Options.filename = "" then begin
    print_string usage;
    exit 1;
  end;

  match !arg_mode with
  | Typecheck
  | TypecheckAndCompile ->
      Options.please_compile := (!arg_mode = TypecheckAndCompile);
      let env =
        Driver.run opts (fun () -> Driver.process !Options.filename)
      in
      if !arg_mode = Typecheck then begin
        if Log.debug_level () <= 0 then
            MzString.bprintf "%a" Driver.print_signature env
        else
          Log.debug ~level:0 "\n%a"
           MzPprint.pdoc (Types.TypePrinter.print_permissions, env)
      end
  | Interpret ->
      Driver.run opts (fun () -> Driver.interpret !Options.filename)
;;
