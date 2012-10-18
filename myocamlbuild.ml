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

open Ocamlbuild_plugin;;
open Command;;

dispatch begin function
| After_rules ->
    flag ["ocaml"; "compile"; "strict_sequence"] (A "-strict-sequence");
    flag ["ocaml"; "compile"; "my_warnings"] (S[A "-w"; A "@1..3@8..12@14..21@23..39"]);
    flag ["ocaml"; "pp"; "use_ulex"] (S[A"camlp4o"; A"ulex/pa_ulex.cma"]);
    dep ["ocaml"; "ocamldep"; "use_ulex"] ["ulex/pa_ulex.cma"];
    ocaml_lib ~tag_name:"use_ulex" "ulexing";
| _ -> ()
end;;
