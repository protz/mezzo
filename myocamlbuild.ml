open Ocamlbuild_plugin;;
open Command;;
dispatch begin function
| After_rules ->
    flag ["ocaml"; "compile"; "strict_sequence"] (A "-strict-sequence");
    flag ["ocaml"; "compile"; "my_warnings"] (S[A "-w"; A "@1..3@9..12@14..21@23..28"]);
    flag ["ocaml"; "pp"; "use_ulex"] (S[A"camlp4o"; A"ulex/pa_ulex.cma"]);
    dep ["ocaml"; "ocamldep"; "use_ulex"] ["ulex/pa_ulex.cma"];
    ocaml_lib ~tag_name:"use_ulex" "ulexing";
| _ -> ()
end;;
