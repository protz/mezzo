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

let _ =
  let arg_filename = ref "" in
  let arg_debug = ref false in
  let usage = "HaMLet: a next-generation version of ML\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse
    [
    "-debug", Arg.Set arg_debug, "output possibly boring debug information";
    "-I", Arg.String Driver.add_include_dir, "include this directory";
    ]
    (fun f ->
      if !arg_filename = "" then
        arg_filename := f
      else
        failwith "Only one filename should be specified.\n"
    )
    usage;
  if !arg_debug then
    Log.enable_debug ();
  let ast, _decls = Driver.lex_and_parse !arg_filename in
  let kenv = WellKindedness.(check_data_type_group empty ast) in
  let facts = FactInference.analyze_data_types kenv in
  let env = Env.create kenv facts in
  ignore env;
  Printf.printf "%s\n" (Bash.box "Kinds");
  Printf.printf "%s\n\n" (Printers.string_of_env kenv);
  Printf.printf "%s\n" (Bash.box "Facts");
  Printf.printf "%s\n\n" (FactInference.string_of_facts kenv facts)
