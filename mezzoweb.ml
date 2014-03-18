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

let output_string (s: string): unit =
  let s = Js.string s |> Js.Unsafe.inject in
  Js.Unsafe.fun_call (Js.Unsafe.variable "mezzo_ui_log") [| s |]
;;

let get_file (f: string): string =
  let f = Js.string f |> Js.Unsafe.inject in
  let mezzo_fs = Js.Unsafe.variable "mezzo_fs" in
  let get = Js.Unsafe.get mezzo_fs "get" in
  Js.Unsafe.fun_call get [| f |] |>
  Js.to_string
;;

let _ =
  let w = Js.Unsafe.coerce Dom_html.window in
  let opts =
    { Driver.html_errors = false; backtraces = false }
  in
  let process f = Driver.run opts (fun () -> Driver.process f) in
  w ## mezzo <- Js.Unsafe.obj [|
    "process",
      Js.wrap_callback process |> Js.Unsafe.inject;
  |]
;;

let _ =
  (* Log.enable_debug 5; *)
  Driver.add_include_dir "corelib";
  Driver.add_include_dir "stdlib";
  Options.js := true;
  JsGlue.output_string_ := output_string;
  JsGlue.get_file_ := get_file;
;;

