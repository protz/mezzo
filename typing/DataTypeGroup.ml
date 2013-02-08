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

open Types
open Expressions

let bind_group_in (points: point list) subst_func_for_thing thing =
  let total_number_of_data_types = List.length points in
  let thing =
    Hml_List.fold_lefti (fun level thing point ->
      let index = total_number_of_data_types - level - 1 in
      subst_func_for_thing (TyOpen point) index thing
    ) thing points
  in
  thing
;;


let bind_group_in_group (points: point list) (group: data_type_group) =
  bind_group_in points tsubst_data_type_group group
;;


let bind_group_definitions (env: env) (points: point list) (group: data_type_group): env =
  List.fold_left2 (fun env point (_, _, def, _, _) ->
    (* Replace the corresponding definition in [env]. *)
    replace_type env point (fun binder ->
      { binder with definition = Some def }
    )
  ) env points group
;;


let bind_group (env: env) (group: data_type_group) =
  (* Allocate the points in the environment. We don't put a definition yet. *)
  let env, points = List.fold_left (fun (env, acc) (name, location, _, fact, kind) ->
    let name = User (env.module_name, name) in
    let env, point = bind_type env name location fact kind in
    env, point :: acc
  ) (env, []) group in
  let points = List.rev points in

  env, points
;;


let bind_group_in_toplevel_items (points: point list) (toplevel_items: toplevel_item list) =
  bind_group_in points tsubst_toplevel_items toplevel_items
;;


let debug_toplevel_items env toplevel_items =
  Log.debug "#### DEBUGGING TOPLEVEL_ITEMS ####\n";
  List.iter (function
    | DataTypeGroup group ->
        Log.debug "%a\n"
          KindCheck.KindPrinter.pgroup (env, group);
    | ValueDeclarations decls ->
        Log.debug "%a\n"
          Expressions.ExprPrinter.pdeclarations (env, decls);
    | PermDeclaration it ->
        Log.debug "%a\n"
          Expressions.ExprPrinter.psigitem (env, it)
  ) toplevel_items;
  Log.debug "#### END DEBUGGING TOPLEVEL_ITEMS ####\n"
;;


let bind_data_type_group
    (env: env)
    (group: data_type_group)
    (toplevel_items: toplevel_item list): env * toplevel_item list * point list =
  (* First, allocate points for all the data types. *)
  let env, points = bind_group env group in
  (* Open references to these data types in the branches themselves, since the
   * definitions are all mutually recursive. *)
  let group = bind_group_in_group points group in
  (* Attach the definitions! *)
  let env = bind_group_definitions env points group in
  (* Now we can perform some more advanced analyses. *)
  let env = FactInference.analyze_data_types env points in
  let env = Variance.analyze_data_types env points in
  if false then debug_toplevel_items env toplevel_items;
  (* Open references to these data types in the rest of the program. *)
  let toplevel_items = bind_group_in_toplevel_items points toplevel_items in
  if false then debug_toplevel_items env toplevel_items;
  (* We're done. *)
  env, toplevel_items, points
;;
