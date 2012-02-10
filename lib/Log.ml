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


let debug_level = ref 0
let enable_debug level = debug_level := level

let debug ?level fmt =
  (* If no level is provided, the message is only displayed in very verbose
   * mode. *)
  let level = Option.map_none 4 level in
  if level <= !debug_level then begin
    Hml_String.bfprintf ~new_line:() stderr fmt
  end else
    Hml_String.biprintf fmt

let error fmt =
  Printf.kbprintf (fun buf -> Buffer.add_char buf '\n'; Buffer.output_buffer stderr buf; assert false) (Buffer.create 16) fmt

let affirm b fmt =
  let open Printf in
  if b then
    ifprintf stdout fmt
  else begin
    kfprintf (fun _ -> assert false) stdout fmt
  end
