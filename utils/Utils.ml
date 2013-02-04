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

(* -------------------------------------------------------------------------- *)

(* try/finally *)

let try_finally f h =
  let result =
    try
      f()
    with e ->
      h();
      raise e
  in
  h();
  result

(* Opening a file, while guaranteeing that the file descriptor will be freed. *)

let with_open_in file_path f =
  let c = open_in file_path in
  try_finally (fun () ->
    f c
  ) (fun () ->
    close_in c
  )

let with_open_out file_path f =
  let c = open_out file_path in
  try_finally (fun () ->
    f c
  ) (fun () ->
    close_out c
  )

(* -------------------------------------------------------------------------- *)

(* Trick from Jacques-Henri: if the backtraces become unusable, call this
 * function. Because we develop in byte-code, it will prevent tail-calls,
 * thus producing better backtraces; in native code, with cross-module
 * optimizations, this will be a no-op. So if your function returns x, just make
 * it return "Utils.dont_inline x". *)
let dont_inline x = x;;

let fresh_name =
  let counter = ref 0 in
  fun prefix ->
    let n = string_of_int !counter in
    counter := !counter + 1;
    prefix ^ n
;;

let fresh_var prefix = Variable.register (fresh_name prefix);;

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

let file_get_contents f =
  with_open_in f read
;;

let ptag buf p =
  let open Obj in
  if is_block (repr p) then
    Printf.bprintf buf "%d-th block constructor" ((tag (repr p) + 1))
  else
    Printf.bprintf buf "%d-th constant constructor" ((magic p) + 1);
;;

let absolute_path p =
  let c = Sys.getcwd () in
  Sys.chdir p;
  let r = Sys.getcwd () in
  Sys.chdir c;
  r
;;
