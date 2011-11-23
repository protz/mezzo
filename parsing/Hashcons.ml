(*****************************************************************************)
(*  HaMLet, a ML dialect with a type-and-capability system                   *)
(*  Copyright (C) 2011 François Pottier, Jonathan Protzenko                  *)
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

type t = (string, int) Hashtbl.t * string InfiniteArray.t * int ref

let create () =
  Hashtbl.create 43, InfiniteArray.make "", ref 0

let add (tbl, rev, counter) key =
  try
    Hashtbl.find tbl key
  with Not_found ->
    let i = !counter in
    incr counter;
    Hashtbl.add tbl key i;
    InfiniteArray.set rev i key;
    i

let find (_, rev, _) i =
  InfiniteArray.get rev i
