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

let fresh_name =
  let counter = ref 0 in
  fun prefix ->
    let n = string_of_int !counter in
    counter := !counter + 1;
    prefix ^ n
;;

let read ic =
  let buf = Buffer.create 4096 in
  let s = String.create 2048 in
  while begin
    let l = input ic s 0 (String.length s) in
    if l > 0 then begin
      Buffer.add_string buf (String.sub s 0 l);
      true
    end else begin
      false
    end
  end do () done;
  Buffer.contents buf
;;

let ptag buf p =
  let open Obj in
  if is_block (repr p) then
    Printf.bprintf buf "%d-th block constructor" ((tag (repr p) + 1))
  else
    Printf.bprintf buf "%d-th constant constructor" ((magic p) + 1);
;;
