(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2014 Jonathan Protzenko and François Pottier               *)
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

(* These functions are only filled in by [MezzoWeb], if compiled. *)

let output_string_: (string -> unit) ref =
  ref (fun _ -> assert false)

let output_string s =
  !output_string_ s

let get_file_: (string -> string) ref =
  ref (fun _ -> assert false)

let get_file f =
  !get_file_ f

let highlight_range_: (Lexing.position -> Lexing.position -> unit) ref =
  ref (fun _ _ -> assert false)

let highlight_range l1 l2 =
  !highlight_range_ l1 l2
