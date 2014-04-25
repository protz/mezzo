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

class type file = object
  method name : Js.js_string Js.t Js.prop
  method content : Js.js_string Js.t Js.prop
end
class type dir = object
  method name : Js.js_string Js.t Js.prop
  method files : file Js.t Js.js_array Js.t Js.prop
end
class type mezzo = object
  method beforeInit : (unit -> unit) Js.callback Js.writeonly_prop
  method afterInit : (unit -> unit) Js.callback Js.writeonly_prop
  method process : (Js.js_string Js.t -> bool Js.t -> bool Js.t -> int -> Js.js_string Js.t -> unit) Js.callback Js.writeonly_prop
  method files: (dir Js.t Js.js_array Js.t) Js.prop
end

let mezzo : mezzo Js.t = Js.Unsafe.global##mezzo <- Js.Unsafe.obj [||]; Js.Unsafe.global##mezzo
let toplevel_filename = "::toplevel.mz"
let toplevel_filename_i = "::toplevel.mzi"

let timestamp_chan = open_out "/dev/null"

let timestamp () =
  let date = jsnew Js.date_now () in
  let ts = Js.to_string (date##toLocaleTimeString()) in
  MzString.bfprintf ~new_line:() timestamp_chan "%s" ts


let process
    (s: Js.js_string Js.t)
    (type_check: bool Js.t)
    (interpret: bool Js.t)
    (debug_level: int)
    (warn_error: Js.js_string Js.t) =
  try
    let s = Js.to_string s in
    let warn_error = Js.to_string warn_error in
    let type_check = Js.to_bool type_check in
    let interpret = Js.to_bool interpret in
    timestamp ();
    let f = toplevel_filename in
    if Sys.file_exists f then Sys.remove toplevel_filename;
    Sys_js.register_file f s;
    Js.Unsafe.global##mezzoReturnCode <- 0;
    let t0 = Sys.time () in
    (* Reset to the default value and then parse the user-provided one. *)
    TypeErrors.parse_warn_error !Options.warn_error;
    TypeErrors.parse_warn_error warn_error;

    (* Debug level. *)
    Log.enable_debug debug_level;

    let opts =
      { Driver.html_errors = false; backtraces = false }
    in
    if type_check then
      ignore (Driver.run opts (fun () -> Driver.process f));
    if interpret then
      Driver.run opts (fun () -> Driver.interpret f);

    let delta = Sys.time () -. t0 in
    let action = match type_check, interpret with
      | true, true -> "Type-checked and interpreted"
      | true, _ ->    "Type-checked"
      | _ , true ->   "Interpreted"
      | false,false -> "Did nothing" in
    if Js.Unsafe.global##mezzoReturnCode = 0 then
      MzString.bprintf "%s successfully (in about %.2fs)\n" action delta
    else
      MzString.beprintf "Mezzo terminated abruptly\n"
  with
  | Js.Error e ->
    MzString.bprintf "Mezzo threw an Exception : %s, %s\n%s\n."
      (Js.to_string e##name)
      (Js.to_string e##message)
      (Js.Optdef.case (e##stack) (fun () -> "Not backtrace") (fun x ->  Js.to_string x) )
  | e ->
    MzString.beprintf "Mezzo threw an Exception : %s\n" (Printexc.to_string e);;


let _ =
  mezzo##beforeInit <- Js.wrap_callback (fun _ ->
      let highlight_range (l1: Lexing.position) (l2: Lexing.position): unit =
        let open Lexing in
        let row1 = l1.pos_lnum - 1 in
        let col1 = l1.pos_cnum - l1.pos_bol in
        let row2 = l2.pos_lnum - 1 in
        let col2 = l2.pos_cnum - l2.pos_bol in
        let hl = Js.Unsafe.variable "mz_highlight_range" in
        Js.Unsafe.fun_call hl (Array.map Js.Unsafe.inject [| row1; col1; row2; col2 |]) in

      JsGlue.highlight_range_ := highlight_range;
      Driver.add_include_dir "corelib";
      Driver.add_include_dir "stdlib";
      Driver.add_include_dir ".";
      Options.js := true;

      let files =
        let dir name =
          let files = Sys.readdir name in
          let files = Array.map (fun file ->
              let content = Js.Unsafe.(fun_call (variable "caml_fs_file_content") [| inject (Js.string (name ^ "/" ^ file)) |]) in
              Js.Unsafe.obj [| "name", Js.Unsafe.inject (Js.string file);
                               "content", Js.Unsafe.inject (Js.string content);|]) files in

          Js.Unsafe.obj [| "name", Js.Unsafe.inject (Js.string name);
                           "files", Js.Unsafe.inject files |] in
        let all = Array.map dir [|"corelib";"stdlib";"demos"|] in
        Js.array all in
      let flusher cl = (fun s ->
          Js.Unsafe.fun_call
            (Js.Unsafe.variable "mz_log")
            (Array.map (fun s -> Js.Unsafe.inject (Js.string s)) [|  s; cl|])) in
      Sys_js.set_channel_flusher stdout (flusher "message");
      Sys_js.set_channel_flusher stderr (flusher "message error-message");
      Sys_js.set_channel_flusher timestamp_chan (flusher "timestamp");
      mezzo##files <- files;
      timestamp ()





    );
  mezzo##afterInit <- Js.wrap_callback (fun _ ->
      MzString.bprintf "Editor successfully loaded, hit Ctrl-M or Command-M.\n";
    );
  mezzo##process <- Js.wrap_callback process
