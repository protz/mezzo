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

let bind_types_in_types =
  (* Then build up the resulting environment. *)
  let tenv, points = List.fold_left (fun (tenv, acc) (name, def, fact, kind) ->
    let name = T.User name in
    let tenv, point = T.bind_type tenv name tenv.T.location ~definition:def fact kind in
    tenv, point :: acc) (tenv, []
  ) translated_definitions in
  let points = List.rev points in

  (* Construct the reverse-map from constructors to points. *)
  let tenv = List.fold_left2 (fun tenv (_, def, _, _) point ->
    match def with
    | None, _ ->
        tenv
    | Some (_, def, _), _ ->
        let type_for_datacon = List.fold_left (fun type_for_datacon (name, _) ->
          T.DataconMap.add name point type_for_datacon
        ) tenv.T.type_for_datacon def in  
        { tenv with T.type_for_datacon }
  ) tenv translated_definitions points in

  (* Finally, open the types in the type definitions themselves. *)
  let total_number_of_data_types = List.length points in
  let tenv = T.fold_types tenv (fun tenv point { T.kind; _ } { T.definition; _ } ->
    match definition with
    | Some (None, _) ->
        (* It's an abstract type, it has no branches where we should perform the
         * opening. *)
        tenv

    | Some (Some (flag, branches, clause), variance) ->
        let arity = T.get_arity_for_kind kind in

        (* Replace each TyVar with the corresponding TyPoint, for all branches. *)
        let branches, clause =
          Hml_List.fold_lefti (fun level (branches, clause) point ->
            (* We need to add [arity] because one has to move up through the type
             * parameters to reach the typed defined at [level]. *)
            let index = total_number_of_data_types - level - 1 + arity in
            (* Perform the substitution. *)
            List.map
              (T.tsubst_data_type_def_branch (T.TyPoint point) index)
              branches,
            Option.map (T.tsubst (T.TyPoint point) index) clause
          ) (branches, clause) points
        in

        (* And replace the corresponding definition in [tenv]. *)
        T.replace_type tenv point (fun binder ->
          { binder with T.definition = Some (Some (flag, branches, clause), variance) }
        )

    | None ->
        Log.error "There should be only type definitions at this stage"
  ) tenv in
;;

let open_types
    (group: data_type_group)
    (points: point list)
    (blocks: block list) =
  let total_number_of_data_types = List.length points in
  let subst_decl = fun declarations ->
    Hml_List.fold_lefti (fun level declarations point ->
      let index = total_number_of_data_types - level - 1 in
      E.tsubst_decl (T.TyPoint point) index declarations
    ) declarations points
  in
  subst_decl declarations
;;

