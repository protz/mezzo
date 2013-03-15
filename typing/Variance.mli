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

(** This module is entirely devoted to computing the variance of type parameters
 * in data types.
 *
 * This module uses [Fix], which we bundle as part of Mezzo. See
 * {{:http://gallium.inria.fr/~fpottier/fix/fix.html.en} Fix's webpage}.
 *)

open TypeCore

(** Compare two variances and tell if the second one subsumes the first one. *)
val leq : variance -> variance -> bool

(** Perform variance computations on a set of data types, and return an
 * environment where variances have been updated. *)
val analyze_data_types : env -> var list -> env
