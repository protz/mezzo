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

(** Some customizations: a custom "my_warnings" tag. *)

open Ocamlbuild_plugin;;
open Command;;

dispatch begin function
| After_rules ->
    flag ["ocaml"; "compile"; "my_warnings"]
      (S[A "-w"; A "@1..3@8..12@14..21@23..39"]);
| _ -> ()
end;;


(** Compiling mz files to ml files, mzi files to mli files. *)

(* As a special case, we check whether there is a [mezzo] executable
   in the current directory [.]. This is useful when building the
   core library and standard library. Otherwise, we assume/hope that
   [mezzo] is in the PATH. *)

let mezzo () =
  if Sys.file_exists "./mezzo" then
    A (Sys.getcwd() ^ "/mezzo")
  else if Sys.file_exists "./mezzo.native" then
    A (Sys.getcwd() ^ "/mezzo.native")
  else
    A "mezzo"

(* This command invokes the Mezzo compiler. *)

let compile env builder =
  Cmd (S [
    mezzo ();
    A "-c";
    P (env "%(path)%(filename).mz");
    Sh ">/dev/null"; (* TEMPORARY we have to suppress Mezzo's verbose output *)
  ])

(* The following two rules tell how to compile [Mezzo] files. If we have
   both [.mz] and [.mzi] files, then we produce both [.ml] and [.mli]
   files. If we have just an [.mz] file, then we produce just an [.ml]
   file. *)

(* TEMPORARY not sure that ocamlbuild understands these overlapping rules; test! *)



let () =
  rule
    "mezzo-mz-mzi" (* the name of the rule, which should be unique *)
    ~deps:[
      "%(path)%(filename).mz";"%(path)%(filename).mzi"
    ](* the source files *)
    ~prods:[
      "%(path:<**/>)mz%(filename:<*> and not <*.*>).ml";
      "%(path:<**/>)mz%(filename:<*> and not <*.*>).mli"
    ] (* the target files *)
    compile

let () =
  rule
    "mezzo-mz" (* the name of the rule, which should be unique *)
    ~deps:[
      "%(path)%(filename).mz"
    ](* the source files *)
    ~prods:[
      "%(path:<**/>)mz%(filename:<*> and not <*.*>).ml";
    ] (* the target files *)
    compile

(* Options for the OCaml compiler. *)

let () =
  dispatch (function
    | After_rules ->
        (* Disable the warning about statements that never return. *)
        flag ["ocaml"; "compile"; "mezzo"] (S[A "-w"; A "-21"]);
        (* Do not load the ocaml core library or the standard library. *)
        flag ["ocaml"; "compile"; "mezzo"] (S[A "-nopervasives"; A "-nostdlib"]);
        flag ["ocaml"; "link"; "mezzo"] (S[A "-nopervasives"; A "-nostdlib"]);
    | _ ->
        ()
  )
