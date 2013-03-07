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

open TypeCore

(* The code is in CPS style, as usual for a hoisting transform. *)

let rec hoist (env : env) (ty : typ) (k : typ -> typ) : typ =
  let ty = modulo_flex env ty in
  match ty with

  (* We stop at (do not go down into) the following constructs. These
     include quantifiers, so there are no name capture problems. They
     also include [TyImply], as it would be logically incorrect to
     hoist a constraint out of an implication. *)

  | TyUnknown
  | TyDynamic
  | TyBound _
  | TyOpen _
  | TyForall _
  | TyExists _
  | TyApp _
  | TySingleton _
  | TyArrow _
  | TyEmpty
  | TyImply _
      -> k ty

  (* We descend into the following constructs, and hoist constraints
     out of them. *)

  | TyTuple tys ->
      MzList.cps_map (hoist env) tys (fun tys ->
      k (TyTuple tys)
      )
  | TyConcreteUnfolded (datacon, fields, clause) ->
      MzList.cps_map (hoist_field env) fields (fun fields ->
      k (TyConcreteUnfolded (datacon, fields, clause))
      )
  | TyBar (ty1, ty2) ->
      hoist env ty1 (fun ty1 ->
      hoist env ty2 (fun ty2 ->
      k (TyBar (ty1, ty2))
      ))
  | TyAnchoredPermission (ty1, ty2) ->
      hoist env ty2 (fun ty2 ->
      k (TyAnchoredPermission (ty1, ty2))
      )
  | TyStar (ty1, ty2) ->
      hoist env ty1 (fun ty1 ->
      hoist env ty2 (fun ty2 ->
      k (TyStar (ty1, ty2))
      ))

  (* This is where we find a constraint and hoist it. *)

  | TyAnd (c, ty) ->
      TyAnd (c, hoist env ty k)

and hoist_field env field k =
  match field with
  | FieldValue (f, ty) ->
      hoist env ty (fun ty ->
      k (FieldValue (f, ty))
      )
  | FieldPermission ty ->
      hoist env ty (fun ty ->
      k (FieldPermission ty)
      )

let hoist env ty =
  hoist env ty (fun ty -> ty)

let rec extract_constraints env ty =
  let ty = modulo_flex env ty in
  match ty with
  | TyAnd (c, ty) ->
      let cs, ty = extract_constraints env ty in
      c :: cs, ty
  | ty ->
      [], ty

