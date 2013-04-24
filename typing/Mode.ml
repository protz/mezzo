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

type mode =
  | ModeBottom
  | ModeDuplicable
  | ModeExclusive
  | ModeAffine

(* Basic operations. *)

let equal : mode -> mode -> bool =
  (=)

let compare : mode -> mode -> int =
  Pervasives.compare

let bottom =
  ModeBottom

let top =
  ModeAffine

let is_maximal = function
  | ModeAffine ->
      true
  | _ ->
      false

let leq m1 m2 =
  match m1, m2 with
  | ModeBottom, _
  | _, ModeAffine
  | ModeDuplicable, ModeDuplicable
  | ModeExclusive, ModeExclusive ->
      true
  | _, _ ->
      false

let meet m1 m2 =
  match m1, m2 with
  | ModeBottom, _
  | _, ModeBottom ->
      ModeBottom
  | ModeAffine, m
  | m, ModeAffine ->
      m
  | _, _ ->
      if m1 = m2 then m1 else ModeBottom

let print = function
  | ModeBottom ->
      "bottom"
  | ModeDuplicable ->
      "duplicable"
  | ModeExclusive ->
      "exclusive"
  | ModeAffine ->
      "affine"

let modes = [
  ModeBottom;
  ModeDuplicable;
  ModeExclusive;
  ModeAffine
]

module ModeMap = struct
  
  include Map.Make(struct
      type t = mode
      let compare = Pervasives.compare
  end)

  (* Building a total map. *)

  let total f =
    List.fold_left (fun accu m ->
      add m (f m) accu
    ) empty modes

  (* Completing a partial map. *)

  let complete f map =
    List.fold_left (fun accu m ->
      if mem m accu then
       accu
      else
       add m (f m) accu
    ) map modes

end
