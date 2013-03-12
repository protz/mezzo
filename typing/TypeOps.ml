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

(* ---------------------------------------------------------------------------- *)

(** [collect t] recursively walks down a type with kind KType, extracts all
    the permissions that appear in it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    KPerm, which represents all the permissions that were just extracted. *)

(** In fact, [collect] also calls itself recursively at kind KPerm, and
    is able to extract permissions out of permissions, e.g., to find a
    TyBar nested inside a TyAnchoredPermission. Because this behavior was
    not documented, I thought it was not essential, but it fact it is. *)

class collect (perms : typ list ref) = object (self)
  inherit [unit] map as super
  (* We re-implement the main visitor method in order to be warned
     about new cases and to share code for some cases. *)
  method visit () ty =
    (* No normalization. *)
    match ty with

      (* We stop at the following constructors. *)

    | TyUnknown
    | TyDynamic
    | TyBound _
    | TyOpen _
    | TyForall _
    | TyExists _
    | TyApp _
    | TySingleton _
    | TyArrow _
    | TyImply _
    | TyEmpty
      -> ty

      (* We descend into the following constructs. *)

    | TyTuple _
    | TyConcreteUnfolded _
    | TyStar _
      -> super#visit () ty

      (* We descend into the right-hand side of [TyAnd] and [TyAnchoredPermission]. *)

    | TyAnd (c, ty) ->
        TyAnd (c, self#visit () ty)
    | TyAnchoredPermission (x, p) ->
        TyAnchoredPermission (x, self#visit () p)

      (* [TyBar] is where the action takes place. *)

    | TyBar (ty, p) ->
        let p = self#visit () p in
	perms := p :: !perms;
	self#visit () ty

  (* At [TyConcreteUnfolded], we set aside the [FieldPermission]s and
     descend into the [FieldValue]s. *)
  method resolved_branch () branch =
    { 
      branch_flavor = branch.branch_flavor;
      branch_datacon = branch.branch_datacon;
      branch_fields = MzList.map_some (function
	| FieldValue (field, ty) ->
            Some (FieldValue (field, self#visit () ty))
	| FieldPermission p ->
	    perms := p :: !perms;
	    None
      ) branch.branch_fields;
      branch_adopts = branch.branch_adopts;
    }

end

let collect (ty : typ) : typ * typ list =
  let perms = ref [] in
  let ty = (new collect perms) # visit () ty in
  ty, !perms

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

  | TyConcreteUnfolded branch ->
      let ts = List.map (function
        | FieldValue (_, t) ->
            t
        | FieldPermission _ ->
            Log.error "[collect] wanted here"
      ) branch.branch_fields in
      let ts = branch.branch_adopts :: ts in
      List.fold_left mark_reachable env ts

  | TySingleton t ->
      mark_reachable env t

  | TyArrow _ ->
      env
;;
