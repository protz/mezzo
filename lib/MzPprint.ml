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

(** This modules exports a modified version of {!PPrint} with extra printers. *)

include PPrint

(* Some Bash-isms *)

type colors = {
  mutable green: document;
  mutable red: document;
  mutable blue: document;
  mutable yellow: document;
  mutable default: document;
  mutable underline: document;
}

let colors = {
  green = empty;
  red = empty;
  blue = empty;
  yellow = empty;
  default = empty;
  underline = empty;
}

let enable_colors () =
  colors.green <- fancystring Bash.colors.Bash.green 0;
  colors.red <- fancystring Bash.colors.Bash.red 0;
  colors.blue <- fancystring Bash.colors.Bash.blue 0;
  colors.yellow <- fancystring Bash.colors.Bash.yellow 0;
  colors.default <- fancystring Bash.colors.Bash.default 0;
  colors.underline <- fancystring Bash.colors.Bash.underline 0;
;;

let disable_colors () =
  colors.green <- empty;
  colors.red <- empty;
  colors.blue <- empty;
  colors.yellow <- empty;
  colors.default <- empty;
  colors.underline <- empty;
;;

let _ =
  if Sys.getenv "TERM" <> "dumb" && Unix.isatty Unix.stdout then
    enable_colors ()

let arrow =
  string "->"
;;

let semisemi =
  twice semi

let ccolon =
  twice colon

let commabreak =
  comma ^^ break 1

let semibreak =
  semi ^^ break 1

let int =
  OCaml.int

let larrow =
  string "<-"
;;

let tagof =
  string "tag of "
;;

let name_gen count =
  (* Of course, won't work nicely if we have more than 26 type parameters... *)
  let alpha = "α" in
  (* Yes I'm using the fact that this is utf8 and that α is two bytes. *)
  let c0 = Char.code alpha.[1] in
  MzList.make count (fun i ->
    let code = c0 + i in
    Printf.sprintf "%c%c" alpha.[0] (Char.chr code)
  )
;;

(* [jump body] either displays a space, followed with [body], followed
   with a space, all on a single line; or breaks a line, prints [body]
   at a greater indentation. *)
let jump ?(indent=2) body =
  jump indent 1 body
;;

let english_join =
  separate2 (string ", ") (string ", and ")

let render doc =
  let buf = Buffer.create 1024 in
  PPrint.ToBuffer.pretty 0.95 Bash.twidth buf doc;
  Buffer.contents buf

let dump (filename : string) (doc : document) =
  let buf = Buffer.create 32768 in
  PPrint.ToBuffer.pretty 0.95 Bash.twidth buf doc;
  Utils.with_open_out filename (fun c ->
    Buffer.output_buffer c buf
  )

(* Parentheses with nesting. Yields either:
   (this)
   or:
   (
     that
   )
*)

let parens_with_nesting contents =
  surround 2 0 lparen contents rparen

(* Braces with nesting. Yields either:
   { this }
   or:
   {
     that
   }
*)

let braces_with_nesting contents =
  surround 2 1 lbrace contents rbrace

let array_with_nesting contents =
  surround 2 1 (string "[|") contents (string "|]")

