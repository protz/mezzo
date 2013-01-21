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

module Make (U : sig end) = struct
 
  (* Create a new instance of the hash-consing facility. *)

  let table =
    Hashcons.create()

  (* Names are represented as integers, but will be exported as
     an abstract type. *)

  type name =
      int
  type t = name

  (* Converting strings to names and back. *)

  let register (s : string) : name =
    Hashcons.add table s

  let print (n : name) : string =
    Hashcons.find table n

  (* Name equality. *)

  let equal (n1 : name) (n2 : name) =
    n1 = n2

  (* Name comparison. *)

  let compare (n1 : name) (n2 : name) =
    if n1 > n2 then 1
    else if n2 > n1 then -1
    else 0

  (* Hashing. *)

  let hash =
    (* Could we use the identity function? *)
    Hashtbl.hash

  (* Maps over names. *)

  module Map = Patricia.Little

  (* Memoization. *)

  let memoize (f : name -> 'a) : name -> 'a =
    let cache = ref Map.empty in
    function (m : name) ->
      try
	Map.find m !cache
      with Not_found ->
	let v = f m in
	cache := Map.add m v !cache;
	v

end

