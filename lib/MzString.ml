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

let replace s1 s2 s =
  let s1 = Str.regexp_string s1 in
  let s = Str.global_replace s1 s2 s in
  s

let substring s i j =
  String.sub s i (j - i)

let split s c =
  let rec break s acc =
    try begin
      let i = String.index s c in 
      let l = String.length s in 
      let s1, s2 = substring s 0 i, substring s (i+1) l in 
      break s2 (s1 :: acc) 
    end with Not_found ->
      s :: acc
  in
  List.rev (break s [])
