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

open Types
open Derivations
open TypePrinter
open MzPprint

let words s = separate space (words s)
let (^^^) x y = x ^^ space ^^ y

let print_judgement env = function
  | JSubType (t1, t2) ->
      words "subtract:" ^^^
      print_type env t1 ^^^ minus ^^^ print_type env t2
  | JSubVar (v, t) ->
      words "from" ^^^ print_point env v ^^^
      words "subtract" ^^^ print_type env t
  | JSubPerm t ->
      words "subtract permission" ^^^ print_type env t
  | JSubFloating t ->
      words "subtract floating permission" ^^^ print_type env t
  | JSubConstraint c ->
      words "satisfy" ^^^ print_constraint env c
  | JSubConstraints cs ->
      let cs = List.map (print_constraint env) cs in
      words "satisfy" ^^^ english_join cs
  | JEqual (t1, t2) ->
      words "prove equality:" ^^^
      print_type env t1 ^^^ equals ^^^ print_type env t2
  | JLt (t1, t2) ->
      words "prove subtyping relation:" ^^^
      print_type env t1 ^^^ utf8string "≤" ^^^ print_type env t2
  | JGt (t1, t2) ->
      words "prove subtyping relation:" ^^^
      print_type env t1 ^^^ utf8string "≥" ^^^ print_type env t2
  | JNothing ->
      empty
  | JAdd t ->
      words "perform:" ^^^ string "P" ^^^ equals ^^^
      string "P" ^^^ utf8string "∗" ^^^ print_type env t
  | JDebug (t1, t2) ->
      words "debug info:" ^^^
      string "t1 =" ^^^ print_type env t1 ^^^
      string "t2 =" ^^^ print_type env t2
  | JArith t ->
      words "prove arithmetic predicate:" ^^^
      print_type env t


let comma_or_newline =
  ifflat commabreak hardline

let rec print_rule (rule_name, derivations) =
  let rule_name = string rule_name in
  string "rule" ^^^ rule_name ^^ comma ^//^
    separate_map comma_or_newline print_derivation derivations

and print_derivation = function
  | Good (env, j, r) ->
      let j = print_judgement env j in
      j ^^^ string "using" ^^^ print_rule r
  | Bad (env, j, rs) ->
      let j = print_judgement env j in
      let reason =
        if List.length rs > 0 then
          words "none of the following worked:" ^//^
            separate_map comma_or_newline print_rule rs
        else
          words "no rule was found"
      in
      words "could not" ^^^ j ^^^ string "because" ^^^ reason

let pderivation buf arg =
  pdoc buf ((fun d -> print_derivation d), arg)
