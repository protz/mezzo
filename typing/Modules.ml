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
let import_interface (env: T.env) (items: E.interface): T.env =
  let open Types in
  let open Expressions in
  (* We demand that [env] have the right module name. *)
  let rec import_items env = function
    | PermDeclaration (name, typ) :: items ->
        (* XXX the location information is probably wildly inaccurate *)
        let binding = User (env.module_name, name), KType, env.location in
        let env, p = bind_var env binding in
        let env = Permissions.add env p typ in
        let items = tsubst_toplevel_items (TyPoint p) 0 items in
        let items = esubst_toplevel_items (EPoint p) 0 items in
        import_items env items

    | DataTypeGroup group :: items ->
        let env, items = DataTypeGroup.bind_data_type_group env group items in
        import_items env items

    | ValueDeclarations _ :: _ ->
        assert false

    | [] ->
        env
  in

  import_items env items
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
