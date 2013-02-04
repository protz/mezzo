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

(* Since each declaration is initially parsed as being in its own group, we need
 * to map over consecutive blocks and group them together. *)
let group (declarations: toplevel_item list): toplevel_item list =
  let rev_g = function
    | DataTypeGroup (loc, gs) ->
        DataTypeGroup (loc, List.rev gs)
    | ValueDeclarations gs ->
        ValueDeclarations (List.rev gs)
    | _ as x ->
        x
  in
  let rev = List.rev_map rev_g in
  let rec group prev next =
    match prev, next with
    | DataTypeGroup (loc, gs) :: prev, DataTypeGroup (loc', g) :: next ->
        group (DataTypeGroup ((fst loc, snd loc'), g @ gs) :: prev) next
    | ValueDeclarations gs :: prev, ValueDeclarations g :: next ->
        group (ValueDeclarations (g @ gs) :: prev) next
    | _, n :: ns ->
        group (n :: prev) ns
    | _, [] ->
        rev prev
  in
  group [List.hd declarations] (List.tl declarations)
;;

let mkinfix e1 o e2 =
  EApply (EVar (Variable.register o), ETuple [e1; e2])
;;

let mk_datacon_reference (d : Datacon.name maybe_qualified) : datacon_reference = {
  datacon_unresolved = d;
  datacon_info = None
};;

let mk_tag_update_info () = {
  is_phantom_update = None
};;

let mk_field field_name = {
  field_name;
  field_offset = None;
};;

(* This auxiliary function identifies expressions that can be copied
   without affecting their semantics (basically, just variables). *)

let rec is_var = function
  | EVar _
  | EQualified _ ->
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
    (fun hole -> ELet (Nonrecursive, [ PVar x, e ], hole)), EVar x

