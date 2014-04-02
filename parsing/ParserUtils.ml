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

open SurfaceSyntax

let var x =
  EVar (Unqualified x)

(* This auxiliary function identifies expressions that can be copied
   without affecting their semantics (basically, just variables). *)

let rec is_var = function
  | EVar _ ->
      true
  | ELocated (e, _) ->
      is_var e
  | _ ->
      false

(* This auxiliary function generates a fresh variable to stand for an
   expression [e], unless [e] is a variable. It returns a pair of a
   context (which inserts zero or one [let]-binding) and an expression. *)

let name (hint : string) e : (expression -> expression) * expression =
  if is_var e then
    (fun hole -> hole), e
  else
    let x = Utils.fresh_var hint in
    (fun hole -> ELet (Nonrecursive, [ PVar x, e ], hole)), var x

let mk_datacon_reference (d : Datacon.name maybe_qualified) : datacon_reference = {
  datacon_unresolved = d;
  datacon_info = None
};;

let mkprefix (o : string) e =
  EApply (var (Variable.register o), e)

let mkinfix e1 (o : string) e2 =
  match o with

  | "&&" ->
      (* Boolean conjunction is macro-expanded. *)
      (* e1 && e2 is sugar for: *)
      (* let x1 = e1 in if x1 then e2 else x1 *)
      let context1, x1 = name "conjunct" e1 in
      context1 (EIfThenElse (false, x1, e2, x1))

  | "||" ->
      (* Boolean disjunction is macro-expanded. *)
      (* e1 || e2 is sugar for: *)
      (* let x1 = e1 in if x1 then x1 else e2 *)
      let context1, x1 = name "conjunct" e1 in
      context1 (EIfThenElse (false, x1, x1, e2))

  | _ ->
      EApply (var (Variable.register o), ETuple [e1; e2])
;;

let mk_tag_update_info () = {
  is_phantom_update = None
};;

let mk_field field_name = {
  field_name;
  field_offset = None;
};;

let rec mktyapp ty1 ty2 =
  match ty1 with
  | TyLocated (ty1, _) ->
      mktyapp ty1 ty2
  | TyApp (ty1, args) ->
      TyApp (ty1, args @ [ ty2 ])
  | _ ->
      TyApp (ty1, [ ty2 ])

let mk_concrete pos (dc, all_fields) adopts =
  let fields = MzList.map_some (function
    | `FieldValue x -> Some x
    | `FieldBindingValue (name, t) ->
        (* Desugar "x:: a" into "x: (=x | x @ a)" *)
        let x = TyVar (Unqualified name) in
        let t = TyBar (
          TySingleton x,
          TyAnchoredPermission (x, t)
        ) in
        Some (name, t)
    | _ -> None
  ) all_fields in
  let binders = MzList.map_some
    (function `FieldBindingValue (name, _) -> Some name | _ -> None)
    all_fields
  in
  let permissions = MzList.map_some
    (function `FieldPermission x -> Some x | _ -> None) all_fields
  in
  let t = TyConcrete (dc, fields, adopts) in
  let t = match permissions with
    | [] ->
        t
    | _ :: _ ->
        TyBar (t, MzList.reduce (fun acc x -> TyStar (acc, x)) permissions)
  in
  let t = List.fold_right (fun name t ->
    TyExists ((name, Kind.KTerm, pos), t)
    ) binders t
  in
  t
