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

type colors = {
  green: string;
  red: string;
  blue: string;
  yellow: string;
  default: string;
  underline: string;
}

let mkcolor x = Printf.sprintf "\x1b[38;5;%dm" x
let colors = {
  green = mkcolor 119;
  red = mkcolor 203;
  blue = mkcolor 81;
  yellow = mkcolor 227;
  underline = "\x1b[4m";
  default = "\x1b[0m";
}

let twidth, theight =
  let height, width = ref 0, ref 0 in
  try
    Scanf.sscanf
      (Ocamlbuild_plugin.run_and_read "stty size")
      "%d %d"
      (fun h w -> width := w; height := h);
    !width, !height
  with
  | Failure _ ->
      24, 80

let box txt =
  let boxw = String.length txt + 4 in
  let whitespace = String.make ((twidth - boxw) / 2) ' ' in
  let charw = String.length "║" in
  let line = "═" in
  let top = String.make (charw * boxw) ' ' in
  for i = 1 to boxw - 2 do
    String.blit line 0 top (i * charw) charw;
  done;
  String.blit "╔" 0 top 0 charw;
  String.blit "╗" 0 top (charw * (boxw - 1)) charw;
  let middle = Printf.sprintf "║ %s ║" txt in
  let bottom = String.make (charw * boxw) ' ' in
  for i = 1 to boxw - 2 do
    String.blit line 0 bottom (i * charw) charw;
  done;
  String.blit "╚" 0 bottom 0 charw;
  String.blit "╝" 0 bottom (charw * (boxw - 1)) charw;
  Printf.sprintf "%s%s%s\n%s%s\n%s%s%s\n"
    colors.blue
    whitespace top whitespace middle whitespace bottom
    colors.default


let reset () =
  ignore (Sys.command "clear")
