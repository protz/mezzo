open Ocamlbuild_plugin;;
open Command;;

let make_flags str =
  let bits = Str.split (Str.regexp " ") str in
  S (List.map (fun x -> A x) bits)

let cflag = make_flags (run_and_read "menhir --suggest-comp-flags --table");;
let blflag = make_flags (run_and_read "menhir --suggest-link-flags-byte --table");;
let olflag = make_flags (run_and_read "menhir --suggest-link-flags-opt --table");;

dispatch begin function
| After_rules ->
    flag ["ocaml"; "compile"; "strict_sequence"] (A "-strict-sequence");
    flag ["ocaml"; "compile"; "my_warnings"] (S[A "-w"; A "@1..3@9..12@14..21@23..28"]);
    flag ["ocaml"; "pp"; "use_ulex"] (S[A"camlp4o"; A"ulex/pa_ulex.cma"]);
    dep ["ocaml"; "ocamldep"; "use_ulex"] ["ulex/pa_ulex.cma"];
    ocaml_lib ~tag_name:"use_ulex" "ulexing";
    flag ["ocaml"; "compile"; "use_menhirlib"] cflag;
    flag ["ocaml"; "link"; "native"] olflag;
    flag ["ocaml"; "link"; "byte"] blflag;
| _ -> ()
end;;
