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

(** This file provides a representation of typing derivations, built by
 * [Permissions]. A typing derivation can either represent success, or failure.
 * This module provides printing functions for derivations. *)

type derivation =
  | Good of env * judgement * rule
    (** We found a rule to apply. *)
  | Bad of env * judgement * rule list
    (** We found either no rule to apply, or we tried several rules, and none of
     * them worked. In that case, we stop recording derivations as soon as we hit
     * a rule that doesn't work; that rule will be the head of the list. *)

and rule =
  rule_instance * derivation list

and rule_instance = string

and judgement =
  | JSubType of typ * typ
  | JSubVar of var * typ
  | JSubPerm of typ
  | JSubFloating of typ
  | JSubConstraint of duplicity_constraint
  | JSubConstraints of duplicity_constraint list
  | JEqual of typ * typ
  | JLt of typ * typ
  | JGt of typ * typ
  | JNothing
  | JAdd of typ


(** We then provide various combinators to write this in a fairly natural
 * manner. The goal is for the user to be able to write:
 *    prove_judgement env (JSubType (t1, t2)) RSubArrow +>>
 *      begin_proof env *>>
 *      sub_type env t'1 t1 *>>
 *      sub_type env t2 t'2
 *
 * *)

(** Primitive operations return a result, that is, either [Some env] along with
 * a good derivation, or [None] with a bad derivation. *)
type result = env option * derivation

let discard_derivation =
  fst

(** If you can find no rule to apply in order to prove this judgement... *)
let no_proof (env: env) (j: judgement): result =
  None, Bad (env, j, [])

(** If you have a series of premises, and want to state that one of them
 * requires nothing to prove... *)
let nothing (env: env) (r: rule_instance): result =
  Some env, Good (env, JNothing, (r, []))

(** Simple composition that discards derivations. Terminate a sequence with
 * [drop]. *)
let ( >>| ) (result: result) (f: env -> env option): env option =
  Option.bind (fst result) f

(** Tie the knot. *)
let drop (env: env): env option =
  Some env

(** Some simple helpers. *)
let is_good_derivation = function Good _ -> true | Bad _ -> false

let is_bad_derivation = function Good _ -> false | Bad _ -> true

let is_good (r: result): bool =
  let env, derivation = r in
  match env with
  | Some _ ->
      Log.check (is_good_derivation derivation) "Inconsistency";
      true
  | None ->
      Log.check (is_bad_derivation derivation) "Inconsistency";
      false

let drop_derivation =
  fst

(** While proving a rule with multiple premises, we use [state]; the first
 * component is used in the fashion of the sequence monad, that is, environments
 * are passed through various stages; the second component is used like the
 * writer monad, that is, much more like an accumulator that stores the
 * derivations. Terminate with [qed]. *)
type state = env option * derivation list

(** Perform an operation on the [env] part of a state without giving any
 * justification for it. *)
let ( >>~ ) (state: state) (f: env -> env): state =
  let env, derivations = state in
  Option.map f env, derivations

(** If you want to apply an axiom. *)
let apply_axiom
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (resulting_env: env): result =
  Some resulting_env, Good (original_env, j, (r, []))

(** If you know how you should prove this, i.e. if you know which rule to
 * apply, call this. *)
let try_proof
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (state: state): result =
  match state with
  | Some final_env, derivations ->
      Log.check (List.for_all is_good_derivation derivations)
        "Inconsistency in [prove_judgement].";
      Some final_env, Good (original_env, j, (r, derivations))
  | None, derivations ->
      if List.length derivations > 0 then
        Log.check (is_bad_derivation (MzList.last derivations))
          "Inconsistency in [prove_judgement]";
      None, Bad (original_env, j, [r, derivations])

(** Composing the premises of a rule. End with [qed]. *)
let ( >>= ) (result: result) (f: env -> state): state =
  let env, derivation = result in
  match env with
  | Some env ->
      let env, derivations = f env in
      env, derivation :: derivations
  | None ->
      (* We're the last derivation that worked, don't bother running the rest of
       * the operations. *)
      None, [derivation]

(** Sometimes it is more convenient to have the premises of a rule as a list. *)
let premises (env: env) (fs: (env -> result) list): state =
  let rec fold env acc fs =
    match fs with
    | [] ->
        (* Everything worked, yay! *)
        Some env, List.rev acc
    | hd :: tl ->
        let env, derivation = hd env in
        match env with
        | Some env ->
            fold env (derivation :: acc) tl
        | None ->
            None, List.rev (derivation :: acc)
  in
  fold env [] fs


(** Tying the knot. *)
let qed (env: env): state =
  Some env, []

(** If you need to fail *)
let fail: state =
  None, []

(** Our other combinator, that allows to explore multiple choices, and either
 * pick the first one that works, or fail by listing all the cases that failed.
 * This one tries multiple instances of the same rule!
 * *)
let try_several
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (l: 'a list)
    (f: 'a -> result)
    (success: env -> 'a list -> 'a -> env): result =
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
      (failed_derivations: derivation list)
      (failed_items: 'a list)
      (remaining: 'a list) =
    match remaining with
    | [] ->
        None, bad failed_derivations
    | item :: remaining ->
        match f item with
        | (Some env, derivation) ->
            let env = success env (List.rev_append failed_items remaining) item in
            Some env, good derivation
        | None, derivation ->
            try_several (derivation :: failed_derivations) (item :: failed_items) remaining
  in
  try_several [] [] l
