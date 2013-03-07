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

(** Various checks that we can't perform until a full environment is ready. *)

open TypeCore
open DeBruijn
open Types
open TypeErrors

let check_adopts_clauses (env: env): unit =
  fold_definitions env (fun () var definition ->
    let kind = get_kind env var in
    match definition with
    | Some (_, _, Some clause), _ ->
        let _return_kind, arg_kinds = flatten_kind kind in
        let arity = List.length arg_kinds in
        let env, vars = make_datacon_letters env kind false in
        let clause = MzList.fold_lefti (fun i clause var ->
          let index = arity - i - 1 in
          tsubst (TyOpen var) index clause
        ) clause vars in
        if not (FactInference.is_exclusive env clause) then
          raise_error env (
            BadFactForAdoptedType (var, clause, FactInference.analyze_type env clause)
          )
    | _ ->
        ()
  ) ()
;;

let check_env (env: env): unit =
  check_adopts_clauses env
;;
