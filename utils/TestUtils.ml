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
open Types

(* This is shared between [testsuite.ml] and [UnitTests.ml] *)
type outcome =
  (* Fail at kind-checking time. *)
  | KFail
  (* Fail at type-checking time. *)
  | Fail of (TypeErrors.raw_error -> bool)
  | Pass

(* Below are mostly facilities for constructing types "by hand". *)

let print_env (env: env) =
  let open TypePrinter in
  Log.debug ~level:1 "%a\n" MzPprint.pdoc (print_permissions, env);
;;

let tuple l =
  TyTuple l
;;

let point x =
  TyOpen x
;;

let points_to x =
  TySingleton (point x)
;;

let permission (p, x) =
  TyAnchoredPermission (p, x)
;;

let user x k =
  User (Module.register "<none>", Variable.register x), k, (Lexing.dummy_pos, Lexing.dummy_pos)
;;

let forall (x, k) t =
  TyQ (
    Forall,
    (user x k),
    UserIntroduced,
    t
  )
;;

let exists (x, k) t =
  TyQ (
    Exists,
    (user x k),
    UserIntroduced,
    t
  )
;;

let var x =
  TyBound x
;;

let bar x p =
  TyBar (x, p)
;;

let empty =
  TyEmpty
;;

let dc env x y =
  TyOpen (point_by_name env (Variable.register x)), Datacon.register y
;;

(* This is right-associative, so you can write [list int @-> int @-> tuple []] *)
let (@->) x y =
  TyArrow (x, y)
;;

let unit =
  tuple []
;;

let concrete datacon fields =
  let branch = {
    branch_flavor = ();
    branch_datacon = datacon;
    branch_fields = fields;
    branch_adopts = ty_bottom;
  } in
  TyConcrete branch
;;

