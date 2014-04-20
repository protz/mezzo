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



let process
    (f: string)
    (type_check: bool)
    (interpret: bool)
    (debug_level: int)
    (warn_error: string) =
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
    Driver.run opts (fun () -> Driver.interpret f)
;;

let toplevel_filename = "::toplevel.mz"
let toplevel_filename_i = "::toplevel.mzi"


let by_id s=
  Js.Opt.get
    (Dom_html.document##getElementById(Js.string s))
    (fun () -> failwith (Printf.sprintf "cannot find dom id %S\n%!" s))

let by_id_coerce s f  =
  Js.Opt.get (Js.Opt.bind (Dom_html.document##getElementById(Js.string s)) f)
    (fun () -> failwith (Printf.sprintf "cannot find dom id %S\n%!" s))


let timestamp () =
  let c = by_id "console" in
  let d = Dom_html.createDiv Dom_html.document in
  d##className <- Js.string "timestamp";
  let date = jsnew Js.date_now () in
  let t = Dom_html.document##createTextNode(
      date##toLocaleTimeString()) in
  Dom.appendChild d t;
  Dom.appendChild c d


let make = ref (fun () -> ())

let setup editor =
  editor##setTheme(Js.string "ace/theme/chrome");
  editor##getSession()##setMode(Js.string "ace/mode/ocaml");
  editor##commands##addCommand(
    Js.Unsafe.(obj [|
        "name", inject (Js.string "make");
        "bindKey", inject (obj [| "win", inject (Js.string "Ctrl-M");
                                  "mac", inject (Js.string "Command-M") |]);
        "exec", inject (fun () -> !make ());
        "readOnly", inject Js._true;
      |]));
  editor##focus()

let make_with_editor editor =
  begin try
      timestamp ();
      editor##clearSelection();
      let t0 = Sys.time () in
      let typecheck = Js.to_bool (by_id_coerce "option-typecheck" Dom_html.CoerceTo.input)##checked in
      let interpret = Js.to_bool (by_id_coerce "option-interpret" Dom_html.CoerceTo.input)##checked in
      Js.Unsafe.global##mezzoReturnCode <- 0;
      if Sys.file_exists toplevel_filename then Sys.remove toplevel_filename;
      Sys_js.register_file toplevel_filename (Js.to_string (editor##getValue()));
      process toplevel_filename
        typecheck
        interpret
        (Js.parseInt ((by_id_coerce "option-debug" Dom_html.CoerceTo.input)##value)) (* debug *)
        (Js.to_string ((by_id_coerce "option-warnerror" Dom_html.CoerceTo.input)##value)); (* warnerr *)
      let delta = Sys.time () -. t0 in
      let action = match typecheck, interpret with
        | true, true -> "Type-checked and interpreted"
        | true, _ ->    "Type-checked"
        | _ , true ->   "Interpreted"
        | false,false -> "Did nothing" in
      if Js.Unsafe.global##mezzoReturnCode = 0 then
        Format.printf "%s successfully (in about %.2fs)@." action delta
      else
        Format.eprintf "Mezzo terminated abruptly@."
    with
    | Js.Error e ->
      Js.debugger ();
      Format.eprintf "Mezzo threw an Exception : %s, %s@.%s@."
        (Js.to_string e##name)
        (Js.to_string e##message)
        (Js.Optdef.case (e##stack) (fun () -> "Not backtrace") (fun x ->  Js.to_string x) );
    | Stack_overflow -> Js.debugger (); ()
    | e ->
      Js.debugger ();
      Format.eprintf "Mezzo threw an Exception : %s@." (Printexc.to_string e)

  end

let span text =
  let span = Dom_html.createSpan Dom_html.document in
  let t = Dom_html.document##createTextNode(Js.string text) in
  Dom.appendChild span t;
  span

let build_explorer editor files =
  let ul = by_id "explorer-list" in
  ignore(Sys.file_exists "corelib/autoload");
  List.iter (fun (dir,files) ->
      let li = Dom_html.createLi Dom_html.document in
      Dom.appendChild ul li;
      Dom.appendChild li (span dir);
      Dom.appendChild li (span " ");
      let collapsed = ref false in
      let a = Dom_html.createA Dom_html.document in
      Dom.appendChild li a;
      a##href <- Js.string "#";
      a##style##fontSize <- Js.string "font-size: 80%";
      a##className <- Js.string "toggle";
      let col_txt = Dom_html.document##createTextNode(Js.string "(collapse)") in
      Dom.appendChild a col_txt;
      let ul = Dom_html.createUl Dom_html.document in
      a##onclick <- Dom_html.handler (fun _ ->
          if not !collapsed
          then begin
            col_txt##data <- Js.string ("(expand)");
            ul##style##display <- Js.string "none"
          end else begin
            col_txt##data <- Js.string ("(collapse)");
            ul##style##display <- Js.string ""
          end;
          collapsed:= not !collapsed;
          Js._true);
      ul##className <- Js.string "file-list";
      Dom.appendChild li ul;
      List.iter (fun file ->
          let fullname = dir ^ "/" ^ file in
          if Sys.file_exists fullname
          then let li = Dom_html.createLi Dom_html.document in
            Dom.appendChild ul li;
            let a = Dom_html.createA Dom_html.document in
            Dom.appendChild li a;
            a##href <- Js.string "#";
            a##onclick <- Dom_html.handler (fun _ ->
                let content = (Js.Unsafe.variable "caml_fs_file_content") (dir ^ "/" ^ file) in
                editor##setValue(Js.string content);
                editor##clearSelection();
                editor##gotoLine(0);
              );
            let t = Dom_html.document##createTextNode(Js.string file) in
            Dom.appendChild a t;
            ()
        ) files;
      ()
    ) files;
  ()

let _ = Dom_html.window##onload <- Dom_html.handler (fun _ ->
    (by_id "command-clear")##onclick <- Dom_html.handler (fun _ ->
      (by_id "console")##innerHTML <- Js.string ""; Js._true);
    (by_id "command-go")##onclick <- Dom_html.handler (fun _ -> !make (); Js._true);
    (by_id_coerce "option-typecheck" Dom_html.CoerceTo.input)##checked <- Js._true;
    (by_id_coerce "option-warnerror" Dom_html.CoerceTo.input)##value <- Js.string "-1+2..4-5+6";
    (by_id "show-more-options")##onclick <- Dom_html.handler (fun _ ->
        (by_id "more-options")##style##display <- Js.string "";
        let _ = (by_id "buttons-wrapper")##removeChild(((by_id "show-more-options") :> (Dom.node Js.t))) in
        Js._true
      );
    timestamp ();
    let editor = Js.Unsafe.global##ace##edit(Js.string "editor") in
    make := (fun () -> make_with_editor editor);
    build_explorer editor Mezzofiles.all;


    let highlight_range (l1: Lexing.position) (l2: Lexing.position): unit =
      let open Lexing in
      let row1 = l1.pos_lnum - 1 in
      let col1 = l1.pos_cnum - l1.pos_bol in
      let row2 = l2.pos_lnum - 1 in
      let col2 = l2.pos_cnum - l2.pos_bol in
      let r = Js.Unsafe.global##ace##require(Js.string "./range")##_Range in
      editor##getSelection()##addRange(Js.Unsafe.new_obj r (Array.map Js.Unsafe.inject [| row1; col1; row2; col2 |])) in
    JsGlue.highlight_range_ := highlight_range;
    Driver.add_include_dir "corelib";
    Driver.add_include_dir "stdlib";
    Driver.add_include_dir ".";
    Options.js := true;

    let flusher _cl = (fun s ->
        let console = by_id "console" in
        let div = Dom_html.createDiv Dom_html.document in
        let txt = Dom_html.document##createTextNode(Js.string s) in
        div##className <- Js.string "message";
        Dom.appendChild div txt;
        Dom.appendChild console div;
        console##scrollTop <- (console##scrollHeight)) in
    Sys_js.set_channel_flusher stdout (flusher "");
    Sys_js.set_channel_flusher stderr (flusher "error-message");


    Format.printf "Editor successfully loaded, hit Ctrl-M or Command-M.@.";
    Js._true
  )
