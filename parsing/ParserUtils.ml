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

let mkfield f = {
  field_name = f;
  field_datacon = Datacon.register "<invalid>"
};;

let mkinfix e1 o e2 =
  EApply (EVar (Variable.register o), ETuple [e1; e2])
;;

let mkdatacon d = {
  datacon_name = d; datacon_previous_name = Datacon.register "<invalid"
};;
