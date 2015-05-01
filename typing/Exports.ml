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

module T = TypeCore

type value_exports = (Variable.name * T.var) list
type datacon_exports = (T.var * Datacon.name * SurfaceSyntax.datacon_info) list

let bind_implementation_values (env: T.env) (exports: value_exports): T.env =
  T.modify_kenv env (fun kenv k ->
    let kenv = List.fold_left (fun kenv (name, var) ->
      KindCheck.bind_nonlocal kenv (name, Kind.KValue, var)
    ) kenv exports in
    k kenv (fun env -> env)
  )

let bind_implementation_types
  (env: T.env)
  (group: T.data_type_group)
  (vars: T.var list)
  (dc_exports: datacon_exports): T.env
=
  let names = List.map
    (fun { TypeCore.data_name; data_kind; _ } -> data_name, data_kind)
    group.TypeCore.group_items
  in

  TypeCore.modify_kenv env (fun kenv k ->
    let kenv = List.fold_left2 (fun kenv (name, kind) var ->
      KindCheck.bind_nonlocal kenv (name, kind, var)
    ) kenv names vars in
    let kenv = List.fold_left (fun kenv (var, dc, dc_info) ->
      KindCheck.bind_nonlocal_datacon kenv dc dc_info var
    ) kenv dc_exports in
    k kenv (fun env -> env)
  )

let bind_interface_value
  (env: T.env)
  (mname: Module.name)
  (name: Variable.name)
  (p: T.var): T.env
=
  T.modify_kenv env (fun kenv k ->
    let kenv = KindCheck.bind_external_name kenv mname name Kind.KValue p in
    k kenv (fun env -> env)
  )

let bind_interface_types
  (env: T.env)
  (mname: Module.name)
  (group: T.data_type_group)
  (vars: T.var list)
  (dc_exports: datacon_exports): T.env
=
  let names = List.map (fun { TypeCore.data_name; data_kind; _ } -> data_name, data_kind) group.TypeCore.group_items in
  T.modify_kenv env (fun kenv k ->
    let kenv = List.fold_left2 (fun kenv (name, kind) var ->
      KindCheck.bind_external_name kenv mname name kind var
    ) kenv names vars in
    let kenv = List.fold_left (fun kenv (var, dc, dc_info) ->
      KindCheck.bind_external_datacon kenv mname dc dc_info var
    ) kenv dc_exports in
    k kenv (fun env -> env)
  )


(* ---------------------------------------------------------------------------- *)

(* Interface-related functions. *)

let find_qualified_var (env: T.env) (mname: Module.name) (name: Variable.name): T.var =
  let open KindCheck in
  let open SurfaceSyntax in
  match find_variable (T.kenv env) (Qualified (mname, name)) with
  | Local _ -> assert false
  | NonLocal p -> p
;;

let find_unqualified_var (env: T.env) (name: Variable.name): T.var =
  let open KindCheck in
  let open SurfaceSyntax in
  match find_variable (T.kenv env) (Unqualified name) with
  | Local _ -> assert false
  | NonLocal p -> p
;;

