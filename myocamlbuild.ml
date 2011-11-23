open Ocamlbuild_plugin;;
open Command;;

let substring s i j =
  String.sub s i (j - i)

type t = Two of string * string | One of string

let split s c =
  let rec split1 s =
    try begin
      let i = String.index s c in
      let l = String.length s in
      Two (substring s 0 i, substring s (i+1) l)
    end with Not_found ->
      One s
  in
  let rec break s acc =
    match split1 s with
    | One s ->
        s :: acc
    | Two (s1, s2) ->
        break s2 (s1 :: acc)
  in
  List.rev (break s [])

let make_flags str =
  let l = String.length str in
  let str = if str.[l - 1] == '\n' then substring str 0 (l-1) else str in
  let bits = split str ' ' in
  S (List.map (fun x -> A x) bits)

let cflags = make_flags (run_and_read "menhir --suggest-comp-flags --table");;
let blflags = make_flags (run_and_read "menhir --suggest-link-flags-byte --table");;
let olflags = make_flags (run_and_read "menhir --suggest-link-flags-opt --table");;

dispatch begin function
| After_rules ->
    flag ["ocaml"; "compile"; "strict_sequence"] (A "-strict-sequence");
    flag ["ocaml"; "compile"; "my_warnings"] (S[A "-w"; A "@1..3@9..12@14..21@23..28"]);
    flag ["ocaml"; "pp"; "use_ulex"] (S[A"camlp4o"; A"ulex/pa_ulex.cma"]);
    dep ["ocaml"; "ocamldep"; "use_ulex"] ["ulex/pa_ulex.cma"];
    ocaml_lib ~tag_name:"use_ulex" "ulexing";
    flag ["ocaml"; "compile"; "use_menhirlib"] cflags;
    flag ["ocaml"; "link"; "use_menhirlib"] cflags;
    flag ["ocaml"; "link"; "native"; "use_menhirlib"] olflags;
    flag ["ocaml"; "link"; "byte"; "use_menhirlib"] blflags;
| _ -> ()
end;;