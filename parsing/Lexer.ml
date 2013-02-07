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
  let start_col = start_pos.pos_cnum - start_pos.pos_bol in
  let end_col = end_pos.pos_cnum - start_pos.pos_bol in (* intentionally [start_pos.pos_bol] *)
  Printf.bprintf buf "File \"%s\", line %i, characters %i-%i:\n"
    filename start_line start_col end_col

let print_position buf lexbuf =
  let open Lexing in
  let start_pos = start_pos lexbuf in
  let end_pos = end_pos lexbuf in
  p buf (start_pos, end_pos)

(* Error handling *)

type error =
  | UnexpectedEndOfComment
  | UnterminatedComment
  | GeneralError of string

exception LexingError of error

let raise_error x =
  raise (LexingError x)

let print_error buf (lexbuf, error) =
  match error with
    | UnexpectedEndOfComment ->
        Printf.bprintf buf "%a\nUnexpected end of comment" print_position lexbuf
    | UnterminatedComment ->
        Printf.bprintf buf "%a\nUnterminated comment" print_position lexbuf
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

(* Simplified OCaml-like table for operators, from
 * http://stackoverflow.com/questions/6150551/ocaml-why-i-cant-use-this-operator-infix
 * *)
let regexp op_prefix = ['!' '~' '?']
let regexp op_infix0 = ['=' '<' '>' '|' '&' '$'] (* left *)
let regexp op_infix1 = ['@' '^'] (* right *)
let regexp op_infix2 = ['+' '-'] (* left *)
let regexp op_infix3 = ['*' '/'] (* left *)
let regexp symbolchar = op_prefix | op_infix0 | op_infix1 | op_infix2 | op_infix3 | ['%' '.' ':']

(* The lexer *)

let rec token = lexer
| linebreak -> break_line lexbuf; token lexbuf
| whitespace -> token lexbuf
| "(*" -> comment 0 lexbuf
| "*)" -> raise_error UnexpectedEndOfComment

| "abstract" -> locate lexbuf ABSTRACT
| "adopts" -> locate lexbuf ADOPTS
| "and" -> locate lexbuf AND
| "as" -> locate lexbuf AS
| "assert" -> locate lexbuf ASSERT
| "begin" -> locate lexbuf BEGIN
| "builtin" -> locate lexbuf BUILTIN
| "consumes" -> locate lexbuf CONSUMES
| "data" -> locate lexbuf DATA
| "duplicable" -> locate lexbuf DUPLICABLE
| "dynamic" -> locate lexbuf DYNAMIC
| "else" -> locate lexbuf ELSE
| "empty" -> locate lexbuf EMPTY
| "end" -> locate lexbuf END
| "exclusive" -> locate lexbuf EXCLUSIVE
| "explain" -> locate lexbuf EXPLAIN
| "fact" -> locate lexbuf FACT
| "fail" -> locate lexbuf FAIL
| "from" -> locate lexbuf FROM
| "fun" | 955 (* λ *) -> locate lexbuf FUN
| "give" -> locate lexbuf GIVE
| "if" -> locate lexbuf IF
| "in" -> locate lexbuf IN
| "let" -> locate lexbuf LET
| "match" -> locate lexbuf MATCH
| "mutable" -> locate lexbuf MUTABLE
| "open" -> locate lexbuf OPEN
| "owns" -> locate lexbuf OWNS
| "perm" -> locate lexbuf KPERM
| "rec" -> locate lexbuf REC
| "tag" whitespace "of" -> locate lexbuf TAGOF
| "take" -> locate lexbuf TAKE
| "taking" -> locate lexbuf TAKING
| "term" -> locate lexbuf KTERM
| "then" -> locate lexbuf THEN
| "to" -> locate lexbuf TO
| "type" | 8727 (* ∗ *) -> locate lexbuf KTYPE
| "unknown" -> locate lexbuf UNKNOWN
| "val" -> locate lexbuf VAL
| "with" -> locate lexbuf WITH

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
| ":=" -> locate lexbuf (OPINFIX0 (utf8_lexeme lexbuf))
| "::" -> locate lexbuf COLONCOLON
| ":" -> locate lexbuf COLON
| ";" -> locate lexbuf SEMI
| "->" | 8594 (* → *) -> locate lexbuf ARROW
| "=>" | 8658 (* ⇒ *) -> locate lexbuf DBLARROW
| "*" -> locate lexbuf STAR
| "=" -> locate lexbuf EQUAL
| "@" -> locate lexbuf AT

| "-" -> locate lexbuf MINUS
| "!=" -> locate lexbuf (OPINFIX0 (utf8_lexeme lexbuf))
| op_prefix symbolchar* -> locate lexbuf (OPPREFIX (utf8_lexeme lexbuf))
| op_infix0 symbolchar* -> locate lexbuf (OPINFIX0 (utf8_lexeme lexbuf))
| op_infix1 symbolchar* -> locate lexbuf (OPINFIX1 (utf8_lexeme lexbuf))
| op_infix2 symbolchar* -> locate lexbuf (OPINFIX2 (utf8_lexeme lexbuf))
| op_infix3 symbolchar* -> locate lexbuf (OPINFIX3 (utf8_lexeme lexbuf))

| int ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))

| lid -> locate lexbuf (LIDENT (utf8_lexeme lexbuf))
| uid -> locate lexbuf (UIDENT (utf8_lexeme lexbuf))
| eof -> locate lexbuf EOF
| _ ->
    raise_error (GeneralError (utf8_lexeme lexbuf))

and comment level = lexer
| "(*" ->
    comment (level+1) lexbuf
| "*)" ->
    assert (level >= 0);
    if level >=1 then
      comment (level-1) lexbuf
    else
      token lexbuf
| linebreak ->
    break_line lexbuf;
    comment level lexbuf
| eof ->
    raise_error UnterminatedComment (* TEMPORARY indiquer où est le début de ce commentaire! *)
| _ ->
    comment level lexbuf



