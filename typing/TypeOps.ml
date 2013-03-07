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

(** A module for performing various transformations on types. *)

open TypeCore
open Types

(** [collect t] recursively walks down a type with kind KType, extracts all
    the permissions that appear into it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    KPerm, which represents all the permissions that were just extracted. *)
let collect (t: typ): typ * typ list =
  let rec collect (t: typ): typ * typ list =
    match t with
    | TyUnknown
    | TyDynamic

    | TyBound _
    | TyOpen _

    | TyForall _
    | TyExists _
    | TyApp _

    | TySingleton _

    | TyArrow _ ->
        t, []

    (* Interesting stuff happens for structural types only *)
    | TyBar (t, p) ->
        let t, t_perms = collect t in
        let p, p_perms = collect p in
        t, p :: t_perms @ p_perms

    | TyTuple ts ->
        let ts, permissions = List.split (List.map collect ts) in
        let permissions = List.flatten permissions in
        TyTuple ts, permissions

    | TyConcreteUnfolded (datacon, fields, clause) ->
        let permissions, values = List.partition
          (function FieldPermission _ -> true | FieldValue _ -> false)
          fields
        in
        let permissions = List.map (function
          | FieldPermission p -> p
          | _ -> assert false) permissions
        in
        let sub_permissions, values =
         List.fold_left (fun (collected_perms, reversed_values) ->
            function
              | FieldValue (name, value) ->
                  let value, permissions = collect value in
                  permissions :: collected_perms, (FieldValue (name, value)) :: reversed_values
              | _ ->
                  assert false)
            ([],[])
            values
        in
        TyConcreteUnfolded (datacon, List.rev values, clause), List.flatten (permissions :: sub_permissions)

    | TyAnchoredPermission (x, t) ->
        let t, t_perms = collect t in
        TyAnchoredPermission (x, t), t_perms

    | TyEmpty ->
        TyEmpty, []

    | TyStar (p, q) ->
        let p, p_perms = collect p in
        let q, q_perms = collect q in
        TyStar (p, q), p_perms @ q_perms

    | TyAnd _
    | TyImply _ ->
        t, []
  in
  collect t
;;

let rec mark_reachable env t =
  let t = modulo_flex env t in
  match t with
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyBound _ ->
      env

  | TyOpen p ->
      if is_marked env p then
        env
      else
        let env = mark env p in
        if is_term env p then
          let permissions = get_permissions env p in
          List.fold_left mark_reachable env permissions
        else
          env

  | TyForall (_, t)
  | TyExists (_, t) ->
      mark_reachable env t

  | TyBar (t1, t2)
  | TyAnchoredPermission (t1, t2)
  | TyStar (t1, t2)
  | TyAnd ((_, t1), t2)
  | TyImply ((_, t1), t2) ->
      List.fold_left mark_reachable env [t1; t2]

  | TyApp (t1, t2) ->
      List.fold_left mark_reachable env (t1 :: t2)

  | TyTuple ts ->
      List.fold_left mark_reachable env ts

  | TyConcreteUnfolded (_, fields, clause) ->
      let ts = List.map (function
        | FieldValue (_, t) ->
            t
        | FieldPermission _ ->
            Log.error "[collect] wanted here"
      ) fields in
      let ts = clause :: ts in
      List.fold_left mark_reachable env ts

  | TySingleton t ->
      mark_reachable env t

  | TyArrow _ ->
      env
;;
