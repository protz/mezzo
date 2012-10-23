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

(** This module helps dealing with interfaces. *)

module S = SurfaceSyntax
module E = Expressions
module T = Types

(* ---------------------------------------------------------------------------- *)

(* Interface-related functions. *)

let get_exports env =
  let open Types in
  let assoc =
    fold env (fun acc point ({ names; _ }, _) ->
      let canonical_names = List.filter is_user names in
      let canonical_names =
        List.map (function User x -> x | _ -> assert false) canonical_names
      in
      List.map (fun x -> x, point) canonical_names :: acc
    ) [] 
  in
  List.flatten assoc
;;


let check (env: T.env) (signature: S.block list) =
  let exports = get_exports env in

  (* As [check] processes one toplevel declaration after another, it first add
   * the name into the translation environment (i.e. after processing [val foo @ τ],
   * [foo] is known to point to a point in [env] in [tsenv]). Second, in
   * order to check [val foo @ τ], it removes [τ] from the list of available
   * permissions for [foo] in [env], which depletes as we go. *)
  let rec check (env: T.env) (tsenv: KindCheck.env) (blocks: S.block list) =
    match blocks with
    | S.PermDeclaration t :: blocks ->
        let x, t = KindCheck.destruct_perm_decl t in
        let k = KindCheck.infer tsenv t in
        let t = TransSurface.translate_type tsenv t in
        let has_same_name (name, p) =
          if Variable.equal name x then
            Some p
          else
            None
        in
        let point =
          match Hml_List.find_opt has_same_name exports with
          | Some point ->
              point
          | None ->
              let open TypeErrors in
              raise_error env (MissingFieldInSignature x)
        in
        let env =
          match Permissions.sub env point t with
          | Some env ->
              env
          | None ->
              let open TypeErrors in
              raise_error env (NoSuchTypeInSignature (x, t))
        in
        let tsenv = KindCheck.bind_external tsenv (x, k) point in
        check env tsenv blocks

    | [] ->
        ()

    | _ ->
        assert false
  in

  check env KindCheck.empty signature
;;
