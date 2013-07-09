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
open Either

module L = BatLazyList

(** The ****** from batteries lied about their implementation of [concat] which
 * is *not* lazy! I wasted 2h+ on this... *)
let lazy_concat (outer: 'a L.t L.t): 'a L.t =
  let open L in
  let rec lazy_concat_aux (inner: 'a L.t) (outer: 'a L.t L.t): 'a L.t = lazy begin
    match next inner with
    | Cons (head, tail) ->
        Cons (head, lazy_concat_aux tail outer)
    | Nil ->
        match next outer with
        | Nil ->
            Nil
        | Cons (head, tail) ->
            !* (lazy_concat_aux head tail)
  end in
  lazy_concat_aux nil outer

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

(** Primitive operations return a result. A result is a lazy list of either a
 * derivation that "worked", meaning we have a "good" environment along with the
 * corresponding derivation, or a derivation that failed, meaning we have no
 * resulting environment. *)
type result = ((env * derivation, derivation) either) L.t

let singleton r = L.cons r L.nil

let option_of_result r =
  try
    match L.find is_left r with
    | Right _ -> assert false
    | Left (env, _) -> Some env
  with Not_found ->
    None

(** If you can find no rule to apply in order to prove this judgement... *)
let no_proof (env: env) (j: judgement): result =
  singleton (Right (Bad (env, j, [])))

(** If you have a series of premises, and want to state that one of them
 * requires nothing to prove... *)
let nothing (env: env) (r: rule_instance): result =
  singleton (Left (env, Good (env, JNothing, (r, []))))

(** Some simple helpers. *)
let is_good_derivation = function Good _ -> true | Bad _ -> false

let is_bad_derivation = function Good _ -> false | Bad _ -> true

let is_good (r: result): bool =
  L.exists is_left r

(** While proving a rule with multiple premises, we use [state]; the first
 * component is used in the fashion of the sequence monad, that is, environments
 * are passed through various stages; the second component is used like the
 * writer monad, that is, much more like an accumulator that stores the
 * derivations. Terminate with [qed]. *)
type state = ((env * derivation list), derivation list) either L.t

(** Perform an operation on the [env] part of a state without giving any
 * justification for it. *)
let ( >>~ ) (state: state) (f: env -> env): state =
  let f = function
    | Right ds ->
        Right ds
    | Left (env, ds) ->
        Left (f env, ds)
  in
  L.map f state

(** If you want to apply an axiom. *)
let apply_axiom
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (resulting_env: env): result =
  singleton (Left (resulting_env, Good (original_env, j, (r, []))))

(** If you know how you should prove this, i.e. if you know which rule to
 * apply, call this. *)
let try_proof
    (original_env: env)
    (j: judgement)
    (r: rule_instance)
    (state: state): result =
  let f = function
    | Left (env, ds) ->
        Log.check (List.for_all is_good_derivation ds) "Inconsistency in [prove_judgement].";
        Left (env, Good (original_env, j, (r, ds)))
    | Right ds ->
        (* The last element of [ds] is a bad derivation! *)
        if List.length ds > 0 then
          Log.check (is_bad_derivation (MzList.last ds)) "Inconsistency in [prove_judgement]";
        Right (Bad (original_env, j, [r, ds]))
  in
  L.map f state

(** Composing the premises of a rule. End with [qed]. *)
let ( >>= ) (result: result) (f: env -> state): state =
  let f = function
    | Right derivation ->
        (* What should we do after an operation that failed? Nothing, that is, not
         * compute the premises after that one. *)
        singleton (Right [derivation])
    | Left (env, derivation) ->
        let choices = L.map (function
          | Right l ->
              (* [l] is a list whose last element is a failed derivation. *)
              Right (derivation :: l)
          | Left (env, derivations) ->
              Left (env, derivation :: derivations)
        ) (f env) in
        choices
  in
  L.map f result |> lazy_concat

(** Tying the knot. *)
let qed (env: env): state =
  singleton (Left (env, []))

(** If you need to fail *)
let fail: state =
  singleton (Right [])

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


let walk original_env j r choices =
  (* When faced with several choices, either some of them in the list are [Good]
   * derivations, which in turn provide a good derivation for the outer rule. *)
  let good derivation =
    Good (original_env, j, (r, [derivation]))
  in
  (* Or none of the choices offered works; in that case, it's failed derivation
   * for the outer rule, which we record along with *all* the failed derivations
   * (« none of the following worked: ... »). *)
  let bad derivations =
    let rules = List.map (fun x -> r, [x]) derivations in
    Bad (original_env, j, rules)
  in

  (* [walk] is the function that implements the construction of a derivation for
   * the outer rule; it lazily pops elements off the front of [choices]; if the
   * element is a good derivation, this means we have at least one good
   * derivation, so just keeping other good derivations is enough. However, if
   * the derivation isn't a good one, [walk] will eagerly try to find a
   * derivation that works until it reaches the end of the list. We eagerly
   * eliminate bad solutions! *)
  let rec walk (failed: derivation list) (remaining: result) =
    lazy begin match !* remaining with
    | L.Nil ->
        (* We've reached the end of the [result] list without finding a good
         * derivation in there. *)
        L.Cons (Right (bad failed), L.nil)
    | L.Cons (hd, tl) ->
        match hd with
        | Left (env, d) ->
            let remaining = L.filter is_left tl in
            let remaining = L.map (function
              | Left (env, d) -> Left (env, good d)
              | Right _ -> assert false
            ) remaining in
            L.Cons (Left (env, good d), remaining)
        | Right d ->
            !* (walk (d :: failed) tl)
    end
  in

  walk [] choices


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
  (* [try_several] is tail-rec (thanks to lazyness) and preserves the order of
   * the initial list (it's important!). Its goal is to lazily map over the list
   * [l] of items, and for each item, call [f] on it. *)
  let rec try_several
      (before: 'a list)
      (after: 'a list): result L.t =
    lazy begin match after with
    | [] ->
        L.Cons (L.nil, L.nil)
    | item :: after ->
        let result = f original_env (List.rev_append before after) item in
        L.Cons (result, try_several (item :: before) after)
    end
  in
  let choices = try_several [] l in
  (* Each call to [f] may return several choices, so we have to flatten that
   * lazy list of lazy lists... *)
  let choices = lazy_concat choices in

  walk original_env j r choices

(** Simple combinator that allows a less fancy combination of several choices.
 * *)
let par env j r (rs: result list): result =
  walk env j r (L.flatten rs)
