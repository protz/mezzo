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

type program =
  block list

and block =
  | DataTypeGroup of data_type_group
  | Declarations of declaration_group

let tsubst_data_type_group (t2: typ) (i: int) (group: data_type_group): data_type_group =
  let group = List.map (function ((name, loc, def, fact, kind) as elt) ->
    match def with
    | None, _ ->
        (* It's an abstract type, it has no branches where we should perform the
         * opening. *)
        elt

    | Some (flag, branches, clause), variance ->
        let arity = get_arity_for_kind kind in

        (* We need to add [arity] because one has to move up through the type
         * parameters to reach the typed defined at [i]. *)
        let index = i + arity in

        (* Replace each TyVar with the corresponding TyPoint, for all branches. *)
        let branches = List.map (tsubst_data_type_def_branch t2 index) branches in

        (* Do the same for the clause *)
        let clause = Option.map (tsubst t2 index) clause in
        
        let def = Some (flag, branches, clause), variance in
        name, loc, def, fact, kind
  ) group in
  group
;;


let rec tsubst_blocks t2 i blocks =
  match blocks with
  | DataTypeGroup group :: blocks ->
      let group = tsubst_data_type_group t2 i group in
      let n = List.length group in
      let blocks = tsubst_blocks t2 (i + n) blocks in
      DataTypeGroup group :: blocks
  | Declarations decls :: blocks ->
      let decls = tsubst_decl t2 i decls in
      let n = n_decls decls in
      let blocks = tsubst_blocks t2 (i + n) blocks in
      Declarations decls :: blocks
  | [] ->
      []
;;

let bind_group_in (env: env) (points: point list) subst_func_for_thing thing =
  let total_number_of_data_types = List.length points in
  let group =
    Hml_List.fold_lefti (fun level group point ->
      let index = total_number_of_data_types - level - 1 in
      subst_func_for_thing (TyPoint point) index thing
    ) thing points
  in
  thing
;;


let bind_group_in_group (env: env) (points: point list) (group: data_type_group) =
  bind_group_in env points tsubst_data_type_group group
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
  let env, points = List.fold_left (fun (env, acc) (name, location, def, fact, kind) ->
    let name = User name in
    let env, point = bind_type env name location fact kind in
    env, point :: acc
  ) (env, []) group in
  let points = List.rev points in

  (* Construct the reverse-map from constructors to points. *)
  let env = List.fold_left2 (fun env (_, _, def, _, _) point ->
    match def with
    | None, _ ->
        env
    | Some (_, def, _), _ ->
        let type_for_datacon = List.fold_left (fun type_for_datacon (name, _) ->
          DataconMap.add name point type_for_datacon
        ) env.type_for_datacon def in  
        { env with type_for_datacon }
  ) env group points in

  env, points
;;


let bind_group_in_blocks (env: env) (points: point list) (blocks: block list) =
  bind_group_in env points tsubst_blocks blocks
;;


let bind_data_type_group
    (env: env)
    (group: data_type_group)
    (blocks: block list): env * program =
  (* First, allocate points for all the data types. *)
  let env, points = bind_group env group in
  (* Open references to these data types in the branches themselves, since the
   * definitions are all mutually recursive. *)
  let group = bind_group_in_group env points group in
  (* Attach the definitions! *)
  let env = bind_group_definitions env points group in
  (* Now we can perform some more advanced analyses. *)
  let env = FactInference.analyze_data_types env points in
  let env = Variance.analyze_data_types env points in
  (* Open references to these data types in the rest of the program. *)
  let blocks = bind_group_in_blocks env points blocks in
  (* We're done. *)
  env, blocks
;;
