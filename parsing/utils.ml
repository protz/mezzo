(*****************************************************************************)
(*  HaMLet, a ML dialect with a type-and-capability system                   *)
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

open Ulexing

type position = {
  mutable line: int;
  mutable start_col: int; (* Start column *)
  mutable end_col: int; (* End column *)
  mutable offset: int; (* Offset holds the offset of the first column of the
  current line *)
  mutable filename: string;
}

let unknown_position = {
  line = -1;
  start_col = -1;
  end_col = -1;
  offset = 0;
  filename = "unknown location";
}

let position = {
  line = 1;
  start_col = 1;
  end_col = 1;
  offset = 0;
  filename = "<dummy>";
}

(* This is just a dirty trick to force a copy of the record containing the
position since it has mutable fields *)
let get_position () = { position with line = position.line }

let print_position buf { line; start_col; end_col; filename; _ } =
  Printf.bprintf buf "File \"%s\", line %i, characters %i-%i:"
    filename line start_col end_col

let print_current_position buf () =
  print_position buf position

let print_position_short buf { line; start_col; filename; _ } =
  Printf.bprintf buf "%s[%i,%i]" filename line start_col

(* Thread-safe, unique-id generator *)
let id () = Oo.id (object end)

