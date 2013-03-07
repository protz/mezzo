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

(* This function hoists [TyAnd] constructs out of a type. This allows mode
   constraints to become visible as early as possible. This can be useful
   when trying to prove that a type admits a certain mode. *)

(* This is a relatively unambitious hoisting transformation: we stop at
   quantifiers (i.e. we do not go down into them, and we do not hoist
   constraints out of them). In principle, we could hoist a constraint
   out of a quantifier if the quantified variable is not free in it; or,
   more generally, we could hoist not only constraints, but also quantifiers,
   up to the toplevel. This would probably be essentially useless, though,
   as we do not expect the programmer to write a mode constraint at an
   unnecessarily deep position, under a quantifier. (Actually, even the
   current transformation might be useless? Well, it will allow us to
   prove, for instance, that {a} (a, (duplicable a | ())) is duplicable.) *)

val hoist: env -> typ -> typ

(* This function extracts the [TyAnd] constructs that are found at the
   root of a type. *)

val extract_constraints: env -> typ -> mode_constraint list * typ

