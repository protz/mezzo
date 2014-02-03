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
 * [Permissions]. A typing derivation can either represent success, or failure. *)

(** {1 The type of derivations} *)

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

val is_bad_derivation: derivation -> bool
val is_good_derivation: derivation -> bool

(** {1 The type of primitive functions} *)

(** Primitive operations return a result. A result is a lazy list of either a
 * derivation that "worked", meaning we have a "good" environment along with the
 * corresponding derivation, or a derivation that failed, meaning we have no
 * resulting environment. *)
type result = ((env * derivation, derivation) either) LazyList.t

(** Here is how to {b not} prove a judgement. This means that you found no rules
 * to apply in order to prove that judgement. *)
val no_proof : env -> judgement -> result

(** This is a way of proving a judgement by using a rule without premises, i.e.
 * an axiom.
 *
 * Please note that:
 *    [apply_axiom env j r sub_env]
 * is equivalent to
 *    [try_proof env j r (qed sub_env)]
 * *)
val apply_axiom :
  env -> judgement -> rule_instance -> env -> result

(** This is another way of proving a judgement, namely by trying several
 * instances of the same rule on different items.
 *
 * [try_several env j r items attempt] will try to prove judgement [j] in
 * environment [env], using rule [r]; for each [item] in [items], it will
 * [attempt item], hoping to find a successful result, passing it [env'] (the
 * resulting environment), [remaining] (the other items), and [item]. If no item
 * in [items] works, the result will be a conjunction of failures. *)
val try_several:
  env ->
  judgement ->
  rule_instance ->
  'a list ->
  (env -> 'a list -> 'a -> result) ->
  result

(** This is a slightly different combinator, that allows you to try several
 * rules to prove the same judgement. *)
val par: env -> judgement -> rule_instance -> result list -> result

(** If you're iterating over a series of premises, it is sometimes convenient to
 * say that one of them requires no special operations because of a certain
 * rule... *)
val nothing : env -> rule_instance -> result

(** {2 Convenient helpers to deal with results} *)

(** Get the [env option] part of a result. *)
val option_of_result : result -> env option

(** This tells whether a result is successful or not. *)
val is_good : result -> bool


(** {1 State, i.e. chaining premises in order to prove a judgement} *)

(** The type of chained premises. *)
type state

(** This is the most frequent way of trying to prove a judgement.
 * [try_proof env j r s] tries to prove judgement [j] in environment [env] by
 * applying rule [r]. The premises of rule [r] are stored in [state]. *)
val try_proof : env -> judgement -> rule_instance -> state -> result

(** The most intuitive way of writing down the premises for a judgement: you
 * just list all the results that have to be successful for this judgement to be
 * true, and [premises] takes care of chaining them left-to-right. *)
val premises : env -> (env -> result) list -> state

(** Use this operator to chain the premises of a rule in a monadic style. You {b
 * must} terminate the sequence of operations by [qed] or [fail]. This operator
 * passes the environments through and accumulates the premises (in case of
 * success), or just discards the remaining premises (in case of failure). *)
val ( >>= ) : result -> (env -> state) -> state

(** This is the final operator that finishes a derivation. *)
val qed : env -> state

(** If a derivation fails... *)
val fail : state

(** {2 Misc.} *)

(** Perform an operation on the [env] part of a state without giving any
 * justification for it. *)
val ( >>~ ) : state -> (env -> env) -> state
