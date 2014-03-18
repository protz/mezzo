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

(* Functions we need to expose to JS for the JS driver to type-check a Mezzo
 * program:
 * - TypeErrors.html_error
 * - TypeErrors.print_error
 * - print a kind error somehow
 * - lex_and_parse
 * - Modules.all_dependencies... ?
 * - KindCheck.check_implementation
 * - TransSurface.translate_implementation
 *)

let error s =
  let s = Js.string s |> Js.Unsafe.inject in
  Js.Unsafe.fun_call (Js.Unsafe.variable "mezzo_ui_log") s
;;

let lex_and_parse s entry_point =
  let s = Js.to_string s in
  let lexbuf = Ulexing.from_utf8_string s in
  Driver.lex_and_parse_raw lexbuf "toplevel" entry_point
;;

let lex_and_parse_implementation _this s =
  lex_and_parse s Grammar.implementation
;;

let check_implementation _this program =
  Driver.check_implementation (Module.register "toplevel") program None
;;

let _ =
  let w = Js.Unsafe.coerce Dom_html.window in
  w ## mezzo <- Js.Unsafe.obj [|
    "lex_and_parse_implementation",
      Js.wrap_meth_callback lex_and_parse_implementation |> Js.Unsafe.inject;
    "check_implementation",
      Js.wrap_meth_callback check_implementation |> Js.Unsafe.inject;
  |]
;;
