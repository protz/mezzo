open Ocamlbuild_plugin

let ocamlc : Command.spec =
  !Options.ocamlc

let () =
  rule
    "mezzo"      (* the name of the rule, which should be unique *)
    ~dep:"%.mz"  (* the source file *)
    ~prod:"%.ml" (* the target file *)
    (fun (env : env) (builder : builder) ->
      Cmd (S [
	A "mezzo"; (* or use V? *)
	A "-c";
	P (env "%.mz");
	Sh ">/dev/null"; (* TEMPORARY suppress Mezzo's verbose output *)
      ]))
