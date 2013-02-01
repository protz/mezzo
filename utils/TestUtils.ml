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

open Types

let print_env (env: env) =
  let open TypePrinter in
  Log.debug ~level:1 "%a\n" pdoc (print_permissions, env);
;;

(* Some OCaml functions that create HaMLeT types. *)

let tuple l =
  TyTuple l
;;

let point x =
  TyPoint x
;;

let points_to x =
  TySingleton (point x)
;;

let permission (p, x) =
  TyAnchoredPermission (p, x)
;;

let forall (x, k) t =
  TyForall (((User (Module.register "<none>", Variable.register x), k, (Lexing.dummy_pos, Lexing.dummy_pos)), CanInstantiate), t)
;;

let var x =
  TyVar x
;;

let dc env x y =
  TyPoint (point_by_name env (Variable.register x)), Datacon.register y
;;

(* This is right-associative, so you can write [list int @-> int @-> tuple []] *)
let (@->) x y =
  TyArrow (x, y)
;;

let ktype =
  SurfaceSyntax.KType
;;

let unit =
  tuple []
;;

let datacon env t d f =
  TyConcreteUnfolded (dc env t d, f, ty_bottom)
;;
