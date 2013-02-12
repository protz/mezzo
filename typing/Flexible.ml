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

(** This module is dedicated to the handling of flexible variables. *)

open TypeCore
open DeBruijn
open Types

(* [has_flexible env t] checks [t] for flexible variables. *)
let has_flexible env t =
  let rec has_flexible t =
    match modulo_flex env t with
    | TyUnknown
    | TyDynamic
    | TyBound _ ->
        false

    | TyOpen p ->
        is_flexible env p

    | TyForall (_, t)
    | TyExists (_, t) ->
        has_flexible t

    | TyBar (t1, t2)
    | TyArrow (t1, t2) ->
        has_flexible t1 || has_flexible t2

    | TyApp (t1, t2) ->
        has_flexible t1 || List.exists has_flexible t2

    | TyTuple components ->
        List.exists has_flexible components

    | TyConcreteUnfolded (_, fields, clause) ->
        let fields = List.map (function
          | FieldValue (_, t)
          | FieldPermission t ->
              has_flexible t
        ) fields in
        let fields = has_flexible clause :: fields in
        List.exists (fun x -> x) fields

    | TySingleton t ->
        has_flexible t

    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        has_flexible t1 || has_flexible t2

    | TyEmpty ->
        false

    | TyAnd (constraints, t)
    | TyImply (constraints, t) ->
        List.exists (fun (_, t) -> has_flexible t) constraints ||
        has_flexible t

  in
  has_flexible t
;;


(* [find_flexible env t] returns the list of points found in [t] that represent
 * flexible variables. *)
let find_flexible env t =
  let rec find_flexible t =
    let t = modulo_flex env t in
    match t with
    | TyUnknown
    | TyDynamic
    | TyBound _ ->
        []

    | TyOpen p ->
        if is_flexible env p then
          [p]
        else
          []

    | TyForall (_, t)
    | TyExists (_, t) ->
        find_flexible t

    | TyBar (t1, t2)
    | TyArrow (t1, t2) ->
        find_flexible t1 @ find_flexible t2

    | TyApp (t1, t2) ->
        find_flexible t1 @ Hml_List.map_flatten find_flexible t2

    | TyTuple components ->
        Hml_List.map_flatten find_flexible components

    | TyConcreteUnfolded (_, fields, clause) ->
        let fields = List.map (function
          | FieldValue (_, t)
          | FieldPermission t ->
              find_flexible t
        ) fields in
        let fields = find_flexible clause :: fields in
        List.flatten fields

    | TySingleton t ->
        find_flexible t

    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        find_flexible t1 @ find_flexible t2

    | TyEmpty ->
        []

    | TyAnd (constraints, t)
    | TyImply (constraints, t) ->
        find_flexible t @
        Hml_List.map_flatten (fun (_, t) -> find_flexible t) constraints
  in
  let points = find_flexible t in
  let rec strip_duplicates acc = function
    | p :: ps ->
        if List.length (List.filter (same env p) ps) > 0 then
          strip_duplicates acc ps
        else
          strip_duplicates (p :: acc) ps
    | [] ->
        acc
  in
  strip_duplicates [] points
;;

(* [generalize_flexible env t] takes all flexible variables in [t] and
 * generalizes them. *)
let generalize env t =
  let flexible = find_flexible env t in
  List.fold_right (fun p t ->
    let x = fresh_auto_var "/g" in
    let k = get_kind env p in
    TyForall (((x, k, location env), CanInstantiate), tpsubst env (TyBound 0) p t)
  ) flexible t
;;
