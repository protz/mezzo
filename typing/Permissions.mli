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

(** This module provides permission manipulation functions. *)

open TypeCore

(** [collect t] recursively walks down a type with kind TYPE, extracts all
    the permissions that appear into it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    PERM, which represents all the permissions that were just extracted.
    
    FIXME: this function should not be exposed. *)
val collect: typ -> typ * typ list

(** [unify env p1 p2] merges two vars, and takes care of dealing with how the
    permissions should be merged. *)
val unify: env -> var -> var -> env

(** [add env var t] adds [t] to the list of permissions for [p], performing all
    the necessary legwork. *)
val add: env -> var -> typ -> env

(** [add_perm env t] adds a type [t] with kind PERM to [env], returning the new
    environment. *)
val add_perm: env -> typ -> env

(** [sub env var t] tries to extract [t] from the available permissions for
    [var] and returns, if successful, the resulting environment. *)
val sub: env -> var -> typ -> env option

(** [sub_type env t1 t2] tries to perform [t1 - t2]. It is up to
 * the caller to "do the right thing" by not discarding [t1] if it was not
 * duplicable. Unifications may be performed, hence the return environment. *)
val sub_type: env -> typ -> typ -> env option

val add_hint: (name option) -> string -> (name option)

(** Strip out all the constraints from a type. *)
val collect_constraints: typ -> typ * duplicity_constraint list

val add_constraints: env -> duplicity_constraint list -> env
val sub_constraints: env -> duplicity_constraint list -> env option

val keep_only_duplicable: env -> env

(**/**)

(** This is for debugging, it runs a consistency check on a given environment. *)
val safety_check: env -> unit
