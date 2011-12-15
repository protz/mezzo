(*****************************************************************************)
(*  ChaML, a type-checker that uses constraints and a kernel language        *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
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

let bsprintf fmt =
  Printf.kbprintf Buffer.contents (Buffer.create 16) fmt

let bfprintf ?new_line oc fmt =
  Printf.kbprintf (fun buf -> Buffer.output_buffer oc buf; if Option.unit_bool new_line then
    output_string oc "\n";) (Buffer.create 16) fmt

let bprintf fmt =
  bfprintf stdout fmt

let beprintf fmt =
  bfprintf stderr fmt

let buf = Buffer.create 0
let biprintf fmt = Printf.ifprintf buf fmt
