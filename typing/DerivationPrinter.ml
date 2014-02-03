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

open TypeCore
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
  | JSubPerms t ->
      words "subtract a set of permissions" ^^^ print_type env (fold_star t)
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


(* A possibly human-readable explanation. *)
type explanation =
  | MissingAnchored of env * var * typ
  | MissingAbstract of env * typ
  | NoRuleForJudgement of derivation
  | NoGoodExplanation

(* We're looking for atomic failures, i.e. a single missing permission, or
 * constraint, that made the whole thing fail. *)
let is_atomic env = function
  | JSubVar (_, t) ->
      List.length (snd (collect t)) = 0
  | JSubPerm p ->
      List.length (flatten_star env p) = 1
  | JSubPerms ps ->
      List.length (MzList.flatten_map (flatten_star env) ps) = 1
  | _ ->
      false

(* This function assumes an atomic judgement. *)
let make_up_explanation env j =
  let anchored_or_abstract t =
    let t = modulo_flex env t in
    let t = expand_if_one_branch env t in
    match t with
    | TyAnchoredPermission (x, t) ->
        MissingAnchored (env, !!x, t)
    | TyApp _ | TyOpen _ ->
        MissingAbstract (env, t)
    | _ ->
        assert false
  in
  match j with
  | JSubVar (x, t) ->
      MissingAnchored (env, x, t)
  | JSubPerm p ->
      anchored_or_abstract p
  | JSubPerms ps ->
      anchored_or_abstract (List.hd ps)
  | _ ->
      assert false

(* For a given derivation, try to find an easily-explainable, single point of
 * failure. *)
let rec gather_explanation derivation =
  match derivation with
  | Bad (env, j, rs) ->
      if is_atomic env j then begin
        Log.debug ~level:4 "This is atomic: %a\n" pdoc (print_judgement env, j);
        make_up_explanation env j
      end else begin
        let explanations = List.map (fun (_rule_name, premises) ->
          let d = MzList.last premises in
          Log.check (is_bad_derivation d) "Inconsistency in the premises of a failed rule.";
          gather_explanation d
        ) rs in
        match explanations with
        | [] ->
            NoRuleForJudgement derivation
        | e :: [] ->
            e
        | _es ->
            (* TODO: figure out if all branches agree on the same point of
             * failure. Possibly hard because of sub-environments that we're
             * going to have to compare. *)
            NoGoodExplanation
      end

  | Good _ ->
      Log.error "This function's only for failed derivations."

let print_stype env t = 
  match ResugarFold.fold_type env t with
  | Some t ->
      SurfaceSyntaxPrinter.print (Resugar.resugar env t)
  | None ->
      SurfaceSyntaxPrinter.print (Resugar.resugar env t)


let print_short d =
  let explanation = gather_explanation d in
  let useful_permission env x =
    let ps = get_permissions env x in
    let ps = List.filter (function
      | TySingleton _ | TyUnknown -> false
      | _ -> true
    ) ps in
    ps
  in
  let possibly_useful_name env x =
    let names = get_names env x in
    let user_names = List.filter is_user names in
    if List.length user_names > 0 then
      List.hd user_names
    else
      List.hd names
  in
  match explanation with
  | MissingAnchored (env, x, t) ->
      let name = possibly_useful_name env x in
      let extra =
        match useful_permission env x with
        | [] ->
            words "because we have nothing"
        | ps ->
            let ps = english_join @@ List.map
              (fun p ->
                print_var env name ^^^ at ^^^ print_stype env p)
              ps
            in
            words "because all we have is: " ^^ nest 2 (
              break 0 ^^
              ps ^^ break 0
            )
      in
      let loc_text =
        let open Lexing in
        let locs = get_locations env x in
        let locs = List.filter (fun ({ pos_fname; _ }, _) -> pos_fname <> "") locs in
        let locs = List.sort (
          fun ({ pos_cnum = x; _ }, { pos_cnum = x'; _ })
              ({ pos_cnum = y; _ }, { pos_cnum = y'; _ }) ->
            if x = y then
              compare x' y'
            else
              compare x y
        ) locs in
        let pos_start, pos_end = List.hd locs in
        string "Variable" ^^^ print_var env name ^^^ string "is defined as follows." ^^ break 0
        ^^ string (MzString.bsprintf "%a" Lexer.p (pos_start, pos_end)) ^^ break 0
        ^^ string (Lexer.highlight_range pos_start pos_end)
      in
      words "Could not obtain the following permission: " ^^ nest 2 (
        break 0 ^^
        print_var env name ^^^ at ^^^
        print_stype env t
      ) ^^ break 0 ^^ extra ^^ break 0 ^^
      loc_text
  | MissingAbstract (env, t) -> 
      words "Could not obtain the following permission: " ^^ break 0 ^^
      print_stype env t
  | NoRuleForJudgement d ->
      words "No idea how to prove the following: " ^^ break 0 ^^
      print_derivation d
  | NoGoodExplanation ->
      words "No good explanation, sorry"

let pshort buf d =
  pdoc buf ((fun () -> print_short d), ())
