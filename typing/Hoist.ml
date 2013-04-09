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

class hoist (env : env) (cs : mode_constraint list ref) = object (self)

  inherit [unit] map as super

  (* We override the main visitor method, in part because we want
     this code to be re-examined when new cases are added, in part
     because this allows us to share the cases where we stop. *)
  method visit () (ty : typ) : 'result =
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
        -> ty

    (* We descend into the following constructs, and hoist constraints
       out of them. *)

    | TyTuple _
    | TyConcrete _
    | TyBar _
    | TyAnchoredPermission _
    | TyStar _
        -> super#visit () ty
    
    (* This is where we find a constraint and hoist it. *)

    | TyAnd (c, ty) ->
        cs := c :: !cs;
        self#visit () ty

end

let hoist (env : env) (ty : typ) : typ =
  let cs = ref [] in
  (* Visit the types. *)
  let ty = (new hoist env cs) # visit () ty in
  (* The mode constraints that were hoisted out are now in [cs]. *)
  List.fold_left (fun ty c -> TyAnd (c, ty)) ty !cs

let rec extract_constraints env ty =
  let ty = modulo_flex env ty in
  match ty with
  | TyAnd (c, ty) ->
      let cs, ty = extract_constraints env ty in
      c :: cs, ty
  | ty ->
      [], ty

