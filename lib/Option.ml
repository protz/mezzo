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

let map f = function
  | None -> None
  | Some v -> Some (f v)

let map_none v = function
  | None -> v
  | Some v -> v

let unit_bool = function
  | None -> false
  | Some () -> true

let extract = function
  | Some v -> v
  | None -> assert false

let iter = fun f -> function
  | Some i -> f i
  | None -> ()

let bind = fun opt f ->
  match opt with
  | None -> None
  | Some x -> f x

let is_some = function Some _ -> true | _ -> false

let flatten = function Some x -> x | None -> None
