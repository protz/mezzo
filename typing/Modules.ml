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

(* I'm defining module abbreviations because we're juggling with all these
 * modules at the same time, and the names conflict (e.g. env, toplevel_item,
 * etc.). *)
module T = Types
module S = SurfaceSyntax
module E = Expressions

(* Used by [Driver], to import the points from a desugared interface into
 * another one, prefixed by the module they belong to, namely [mname]. *)
let import_interface (_env: T.env) (_iface: Module.name * E.interface): T.env =
  assert false
;;

(* For internal use only (yet). *)
let collect_dependencies (_items: S.toplevel_item list): Module.name list =
  assert false
;;

(* Called by [Driver], returns all the dependencies (transitive) of [items],
 * sorted by topological order. *)
let all_dependencies (_items: S.toplevel_item list): Module.name list =
  assert false
;;
