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

(** This module analyzes data type declaration to synthetize facts about the
   data types. *)

(** This function performs the elaboration phase where we build up more precise
 * facts about the various data types defined in the environment. *)
val analyze_data_types: Types.env -> Types.point list -> Types.env

(** Get the fact for a type, which you can then pass to {Types.fact_leq}. *)
val analyze_type: Types.env -> Types.typ -> Types.fact

(** Is this type duplicable? *)
val is_duplicable: Types.env -> Types.typ -> bool

(** Is this type exclusive? *)
val is_exclusive: Types.env -> Types.typ -> bool
