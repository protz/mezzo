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
  | JSubConstraint of duplicity_constraint
  | JSubConstraints of duplicity_constraint list


(** We then provide various combinators to write this in a fairly natural
 * manner. The goal is for the user to be able to write:
 *    prove_judgement env (JSubType (t1, t2)) RSubArrow +>>
 *      begin_proof env *>>
 *      sub_type env t'1 t1 *>>
 *      sub_type env t2 t'2
 *
 * *)

let is_good_derivation = function Good _ -> true | Bad _ -> false
let is_bad_derivation = function Good _ -> false | Bad _ -> true

let prove_judgement
    (env: env)
    (j: judgement)
    (r: rule_instance): env * judgement * rule_instance =
  env, j, r

type state = env option * derivation list
type result = env option * derivation

let begin_proof (env: env): state =
  Some env, []

let axiom (env: env): state =
  begin_proof env

let failed_proof: state =
  None, []

let no_proof_for_judgement (env: env) (j: judgement): result =
  None, Bad (env, j, [])

let ( *>> ) ((env, derivations): state) (f: env -> result): state =
  match env with
  | Some env ->
      let env, derivation = f env in
      env, derivation :: derivations
  | None ->
      None, derivations

let ( +>> ) (original_env, j, r) ((env, derivations): state): result =
  match env with
  | Some env ->
      Log.check (List.for_all is_good_derivation derivations)
        "Returning Some env means only good derivations";
      let derivation = Good (original_env, j, (r, derivations)) in
      Some env, derivation
  | None ->
      Log.check (is_bad_derivation (List.hd derivations))
        "Returning None means bad derivation";
      let derivation = Bad (original_env, j, [r, derivations]) in
      None, derivation

let try_several
    (l: 'a list)
    (f: 'a -> env option * derivation)
    (success: env -> 'a list -> 'a -> env): env option * derivation list =
  let rec try_several
      (failed_derivations: derivation list)
      (failed_items: 'a list)
      (remaining: 'a list) =
    match remaining with
    | [] ->
        None, failed_derivations
    | hd :: tl ->
        match f hd with
        | (Some env, derivation) ->
            let env = success env (List.rev_append failed_items remaining) hd in
            Some env, [derivation]
        | None, derivation ->
            try_several (derivation :: failed_derivations) (hd :: failed_items) tl
  in
  try_several [] [] l
