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

open Ulexing
open Grammar

(* Keyword recognition. *)

(* The list of keywords is in the file [Keywords], from which the file
   [Keywords.ml] is auto-generated. *)

let keywords : (string, token) Hashtbl.t =
  let keywords = Hashtbl.create 13 in
  List.iter (fun (keyword, token) ->
    Hashtbl.add keywords keyword token
  ) Keywords.keywords;
  keywords

(* Position handling *)

let pos_fname = ref "<dummy>"
let pos_lnum = ref 1
let pos_bol = ref 0
let pos pos_cnum =
  let open Lexing in {
    pos_fname = !pos_fname;
    pos_lnum = !pos_lnum;
    pos_bol = !pos_bol;
    pos_cnum;
  }

let init file_name =
  pos_fname := file_name;
  pos_lnum := 1;
  pos_bol := 0

let start_pos lexbuf = pos (lexeme_start lexbuf)
let end_pos lexbuf = pos (lexeme_end lexbuf)

let locate lexbuf token =
  (token, start_pos lexbuf, end_pos lexbuf)

let break_line lexbuf =
  pos_lnum := !pos_lnum + 1;
  pos_bol := lexeme_end lexbuf

let p buf (start_pos, end_pos: Lexing.position * Lexing.position) =
  let open Lexing in
  let filename = start_pos.pos_fname in
  let start_line = start_pos.pos_lnum in
  let end_line = end_pos.pos_lnum in
  let start_col = start_pos.pos_cnum - start_pos.pos_bol in
  let end_col = end_pos.pos_cnum - end_pos.pos_bol in
  if start_line = end_line then
    Printf.bprintf buf "File \"%s\", line %i, characters %i-%i:\n"
      filename start_line start_col end_col
  else
    Printf.bprintf buf "File \"%s\", line %i, char %i to line %i, char %i:\n"
      filename start_line start_col end_line end_col

let print_position buf lexbuf =
  let open Lexing in
  let start_pos = start_pos lexbuf in
  let end_pos = end_pos lexbuf in
  p buf (start_pos, end_pos)

(* Error handling *)

type error =
  | UnexpectedEndOfComment
  | UnterminatedComment of (Lexing.position * Lexing.position)
  | GeneralError of string

exception LexingError of error

let raise_error x =
  raise (LexingError x)

let print_error buf (lexbuf, error) =
  match error with
    | UnexpectedEndOfComment ->
        Printf.bprintf buf "%a\nUnexpected end of comment" print_position lexbuf
    | UnterminatedComment positions ->
        Printf.bprintf buf "%a\nUnterminated comment" p positions
    | GeneralError e ->
        Printf.bprintf buf "%a\nLexing error: %s" print_position lexbuf e

(* Various regexps *)

let regexp whitespace = ['\t' ' ']+
let regexp linebreak = ['\n' '\r' "\r\n"]
let regexp low_greek = [945-969]
let regexp up_greek = [913-937]
let regexp greek = low_greek | up_greek
let regexp low_alpha = ['a'-'z']
let regexp up_alpha =  ['A'-'Z']
let regexp alpha = low_alpha | up_alpha
let regexp alpha_greek = alpha | greek
let regexp digit = ['0'-'9']
let regexp int = digit+
let regexp lid =
  (low_alpha | low_greek | '_') alpha_greek* (['_' '\''] | alpha_greek | digit)*
let regexp uid =
  (up_alpha | up_greek | '_') alpha_greek* (['_' '\''] | alpha_greek | digit)*

(* The classification of operators is a refinement of OCaml's. *)

(* In OCaml, all operators whose name begins with '=', '<', '>', '|',
   '&', '$' are at level 0, which I believe is quite strange. This
   forces OCaml to make special cases for the operators '||', '&&',
   and '&'. I take the liberty to divide OCaml's level 0 into four
   further sub-levels. *)

let regexp op_prefix  = ['!' '~' '?']
let regexp op_infix0a = ['|'] (* left *)
let regexp op_infix0b = ['&'] (* left *)
let regexp op_infix0c = ['=' '<' '>'] (* nonassoc *)
let regexp op_infix0d = ['$'] (* left *)

let regexp op_infix0  = op_infix0a | op_infix0b | op_infix0c | op_infix0d
let regexp op_infix1  = ['@' '^'] (* right *)
let regexp op_infix2  = ['+' '-'] (* left *)
let regexp op_infix3  = ['*' '/' '%'] (* left *)
let regexp symbolchar = op_prefix | op_infix0 | op_infix1 | op_infix2 | op_infix3 | ['.' ':']

(* The lexer *)

let rec token = lexer
| linebreak -> break_line lexbuf; token lexbuf
| whitespace -> token lexbuf
| "(*" -> comment [(start_pos lexbuf, end_pos lexbuf)] lexbuf
| "*)" -> raise_error UnexpectedEndOfComment

(* Unicode aliases. *)
| 955 (* λ *) -> locate lexbuf FUN
| 8727 (* ∗ *) -> locate lexbuf TYPE

(* A special multi-word keyword. *)
| "tag" whitespace "of" -> locate lexbuf TAGOF

| "<-" -> locate lexbuf LARROW
| "." -> locate lexbuf DOT
| "|" -> locate lexbuf BAR
| "_" -> locate lexbuf UNDERSCORE

| "[" -> locate lexbuf LBRACKET
| "]" -> locate lexbuf RBRACKET
| "{" -> locate lexbuf LBRACE
| "}" -> locate lexbuf RBRACE
| "(" -> locate lexbuf LPAREN
| ")" -> locate lexbuf RPAREN

| "," -> locate lexbuf COMMA
| ":=" -> locate lexbuf (COLONEQUAL (utf8_lexeme lexbuf))
| "::" -> locate lexbuf COLONCOLON
| ":" -> locate lexbuf COLON
| ";" -> locate lexbuf SEMI
| "->" | 8594 (* → *) -> locate lexbuf ARROW
| "=>" | 8658 (* ⇒ *) -> locate lexbuf DBLARROW
| "*" -> locate lexbuf (STAR (utf8_lexeme lexbuf))
| "=" -> locate lexbuf (EQUAL (utf8_lexeme lexbuf))
| "@" -> locate lexbuf AT

| "-" -> locate lexbuf (MINUS (utf8_lexeme lexbuf))
| "+" -> locate lexbuf (PLUS (utf8_lexeme lexbuf))
| "!=" -> locate lexbuf (OPINFIX0c (utf8_lexeme lexbuf))
| op_prefix symbolchar* -> locate lexbuf (OPPREFIX (utf8_lexeme lexbuf))
| op_infix0a symbolchar* -> locate lexbuf (OPINFIX0a (utf8_lexeme lexbuf))
| op_infix0b symbolchar* -> locate lexbuf (OPINFIX0b (utf8_lexeme lexbuf))
| op_infix0c symbolchar* -> locate lexbuf (OPINFIX0c (utf8_lexeme lexbuf))
| op_infix0d symbolchar* -> locate lexbuf (OPINFIX0d (utf8_lexeme lexbuf))
| op_infix1 symbolchar* -> locate lexbuf (OPINFIX1 (utf8_lexeme lexbuf))
| op_infix2 symbolchar* -> locate lexbuf (OPINFIX2 (utf8_lexeme lexbuf))
| "**" symbolchar *     -> locate lexbuf (OPINFIX4 (utf8_lexeme lexbuf))
| op_infix3 symbolchar* -> locate lexbuf (OPINFIX3 (utf8_lexeme lexbuf))

| int ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))

| lid -> locate lexbuf (
           let s = utf8_lexeme lexbuf in
           try Hashtbl.find keywords s with Not_found -> LIDENT s
         )
| uid -> locate lexbuf (UIDENT (utf8_lexeme lexbuf))
| eof -> locate lexbuf EOF
| _ ->
    raise_error (GeneralError (utf8_lexeme lexbuf))

(* [stack] is a non-empty stack of opening comment positions. *)
and comment stack = lexer
| "(*" ->
    comment ((start_pos lexbuf, end_pos lexbuf) :: stack) lexbuf
| "*)" ->
    begin match stack with
    | [ _ ] ->
        (* Back to normal mode. *)
        token lexbuf
    | _ :: stack ->
        (* Continue in comment mode, one level down. *)
        comment stack lexbuf
    | [] ->
        (* Impossible. *)
        assert false
    end
| linebreak ->
    break_line lexbuf;
    comment stack lexbuf
| eof ->
    begin match stack with
    | positions :: _ ->
        raise_error (UnterminatedComment positions)
    | [] ->
        (* Impossible. *)
        assert false
    end
| _ ->
    comment stack lexbuf



