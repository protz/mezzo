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
open Either

(** This file provides a representation of typing derivations, built by
 * [Permissions]. A typing derivation can either represent success, or failure.
 * This module provides printing functions for derivations. *)

type derivation =
  | Good of env * judgement * rule
    (** We found a rule to apply. *)
  | Bad of env * judgement * rule list
    (** We found either no rule to apply, or we tried several rules, and none of
     * them worked. In that case, we stop recording derivations as soon as we hit
     * a rule that doesn't work; that rule will be the tail of the list. *)

and rule =
  rule_instance * derivation list

and rule_instance = string

and judgement =
  | JSubType of typ * typ
  | JSubVar of var * typ
  | JSubPerm of typ
  | JSubPerms of typ list
  | JSubFloating of typ
  | JSubConstraint of mode_constraint
  | JSubConstraints of mode_constraint list
  | JEqual of typ * typ
  | JLt of typ * typ
  | JGt of typ * typ
  | JNothing
  | JAdd of typ
  | JDebug of typ * typ

(** Primitive operations return a result. A result is either a list of good
 * derivations along with the corresponding environment (we may have several
 * choices to pick from) or a failed derivation that serves as an example of how
 * an operation failed (we don't keep *all* the failed derivations). *)
type result = ((env * derivation) list, derivation) either

let drop_derivation = function
  | Left choices ->
      Some (fst (List.hd choices))
  | Right _ ->
      None

(** If you can find no rule to apply in order to prove this judgement... *)
let no_proof (env: env) (j: judgement): result =
  Right (Bad (env, j, []))

(** If you have a series of premises, and want to state that one of them
 * requires nothing to prove... *)
let nothing (env: env) (r: rule_instance): result =
  Left [env, Good (env, JNothing, (r, []))]

(** Some simple helpers. *)
let is_good_derivation = function Good _ -> true | Bad _ -> false

let is_bad_derivation = function Good _ -> false | Bad _ -> true

let is_good (r: result): bool =
  match r with
  | Left choices ->
      Log.check (List.for_all (fun (_, d) -> is_good_derivation d) choices) "Inconsistency";
      true
  | Right derivation ->
      Log.check (is_bad_derivation derivation) "Inconsistency";
      false

(** While proving a rule with multiple premises, we use [state]; the first
 * component is used in the fashion of the sequence monad, that is, environments
 * are passed through various stages; the second component is used like the
 * writer monad, that is, much more like an accumulator that stores the
 * derivations. Terminate with [qed]. *)
type state = ((env * derivation list) list, derivation list) either

(** Perform an operation on the [env] part of a state without giving any
 * justification for it. *)
let ( >>~ ) (state: state) (f: env -> env): state =
  match state with
  | Right _ ->
      state
  | Left choices ->
      Left (List.map (fun (env, ds) -> f env, ds) choices)

(** If you want to apply an axiom. *)
let apply_axiom
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (resulting_env: env): result =
  Left [resulting_env, Good (original_env, j, (r, []))]

(** If you know how you should prove this, i.e. if you know which rule to
 * apply, call this. *)
let try_proof
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (state: state): result =
  match state with
  | Left choices ->
      let choices = List.map (fun (env, derivations) ->
        Log.check (List.for_all is_good_derivation derivations) "Inconsistency in [prove_judgement].";
        env, Good (original_env, j, (r, derivations))
      ) choices in
      Left choices
  | Right ds ->
      (* The last element of [ds] is a bad derivation! *)
      if List.length ds > 0 then
        Log.check (is_bad_derivation (MzList.last ds)) "Inconsistency in [prove_judgement]";
      Right (Bad (original_env, j, [r, ds]))

(** Composing the premises of a rule. End with [qed]. *)
let ( >>= ) (result: result) (f: env -> state): state =
  match result with
  | Right derivation ->
      (* What should we do after an operation that failed? Nothing, that is, not
       * compute the premises after that one. *)
      Right [derivation]
  | Left choices ->
      let choices = List.map (fun (env, derivation) ->
        match f env with
        | Right l ->
            (* [l] is a list whose last element is a failed derivation. *)
            Right (derivation :: l)
        | Left choices ->
            Left (List.map (fun (env, derivations) -> env, derivation :: derivations) choices)
      ) choices in
      Log.check (List.length choices > 0) "Inconsistency";
      if List.for_all is_right choices then
        (* Starting from [result], we can find no good derivation. Just keep one
         * so as to give it to the user. *)
        List.hd choices
      else
        let choices = List.filter is_left choices in
        Left (MzList.flatten_map (function
          | Right _ -> assert false
          | Left choices ->
              choices
        ) choices)

(** Tying the knot. *)
let qed (env: env): state =
  Left [env, []]

(** If you need to fail *)
let fail: state =
  Right []

(** Sometimes it is more convenient to have the premises of a rule as a list. *)
let premises (env: env) (fs: (env -> result) list): state =
  let rec wrap_bind env fs =
    match fs with
    | [] ->
        qed env
    | f :: fs ->
        f env >>= fun env ->
        wrap_bind env fs
  in
  wrap_bind env fs


(** Our other combinator, that allows to explore multiple choices, and either
 * pick the first one that works, or fail by listing all the cases that failed.
 * This one tries multiple instances of the same rule!
 * *)
let try_several
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (l: 'a list)
    (f: env -> 'a list -> 'a -> result): result =
  let good derivation =
    Good (original_env, j, (r, [derivation]))
  in
  let bad derivations =
    (* Remember, this is not *several failed premises*, it is several failed
     * derivations of the same rule! *)
    let rules = List.map (fun x -> r, [x]) derivations in
    Bad (original_env, j, rules)
  in
  let rec try_several
      (acc: result list)
      (before: 'a list)
      (after: 'a list) =
    match after with
    | [] ->
        acc
    | item :: after ->
        let r = f original_env (List.rev_append before after) item in
        try_several (r :: acc) (item :: before) after
  in
  let choices = try_several [] [] l in
  if List.for_all is_right choices then
    let choices = List.map (function
      | Right d ->
          d
      | Left _ ->
          assert false
    ) choices in
    Right (bad choices)
  else
    let choices = List.filter is_left choices in
    Left (MzList.flatten_map (function
      | Right _ -> assert false
      | Left choices ->
          List.map (fun (env, d) -> env, good d) choices
    ) choices)
