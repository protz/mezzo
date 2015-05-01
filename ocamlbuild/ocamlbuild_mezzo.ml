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

(** Compiling mz files to ml files, mzi files to mli files. *)

open Ocamlbuild_plugin;;
open Command;;

(* As a special case, we check whether there is a [mezzo] executable
   in the current directory [.]. This is useful when building the
   core library and standard library. Otherwise, we assume/hope that
   [mezzo] is in the PATH. *)

let apply_rules_and_flags ~boot event =
  match event with
  | After_rules ->
      let mezzo =
        if boot then
          A (Sys.getcwd() ^ "/_build/mezzo.native")
        else
          A "mezzo"
      in

      (* This command invokes the Mezzo compiler. *)

      let compile env _builder =
        Cmd (S [
          mezzo;
          if boot then A "-boot" else N;
          A "-c";
          P (env "%(path)%(filename).mz");
          Sh ">/dev/null"; (* TEMPORARY we have to suppress Mezzo's verbose output *)
        ])
      in

      (* The following two rules tell how to compile [Mezzo] files. If we have
         both [.mz] and [.mzi] files, then we produce both [.ml] and [.mli]
         files. If we have just an [.mz] file, then we produce just an [.ml]
         file. *)

      (* TEMPORARY not sure that ocamlbuild understands these overlapping rules; test! *)

      rule
        "mezzo-mz-mzi" (* the name of the rule, which should be unique *)
        ~deps:[
          "%(path)%(filename).mz";"%(path)%(filename).mzi"
        ](* the source files *)
        ~prods:[
          "%(path:<**/>)mz_%(filename:<*> and not <*.*>).ml";
          "%(path:<**/>)mz_%(filename:<*> and not <*.*>).mli"
        ] (* the target files *)
        compile;

      rule
        "mezzo-mz" (* the name of the rule, which should be unique *)
        ~deps:[
          "%(path)%(filename).mz"
        ](* the source files *)
        ~prods:[
          "%(path:<**/>)mz_%(filename:<*> and not <*.*>).ml";
        ] (* the target files *)
        compile;

      (* Options for the OCaml compiler. *)

      (* Disable the warning about statements that never return. *)
      flag ["ocaml"; "compile"; "mezzo"] (S[A "-w"; A "-21"]);
      (* Do not load the ocaml core library or the standard library. *)
      flag ["ocaml"; "compile"; "mezzo"] (S[A "-nopervasives"; A "-nostdlib"]);
      flag ["ocaml"; "link"; "mezzo"] (S[A "-nopervasives"; A "-nostdlib"]);

  | _ ->
      ()
;;

