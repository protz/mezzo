open Ocamlbuild_plugin

(* TEMPORARY not sure that ocamlbuild understands these overlapping rules *)
(* TEMPORARY how to find correct command name for mezzo? *)

let () =
  rule
    "mezzo-mz-mzi"      (* the name of the rule, which should be unique *)
    ~deps:["%.mz";"%.mzi"]  (* the source files *)
    ~prods:["%.ml";"%.mli"] (* the target files *)
    (fun (env : env) (builder : builder) ->
      Cmd (S [
	A "mezzo";       (* or use V? *)
	A "-c";
	P (env "%.mz");
	Sh ">/dev/null"; (* TEMPORARY suppress Mezzo's verbose output *)
      ]))

let () =
  rule
    "mezzo-mz"      (* the name of the rule, which should be unique *)
    ~dep:"%.mz"  (* the source file *)
    ~prod:"%.ml" (* the target file *)
    (fun (env : env) (builder : builder) ->
      Cmd (S [
	A "mezzo";       (* or use V? *)
	A "-c";
	P (env "%.mz");
	Sh ">/dev/null";
      ]))

(* Options for ocamlc *)

let () =
  dispatch (function
    | After_rules ->
        (* Disable the warning about statements that never return. *)
        flag ["ocaml"; "compile"] (S[A "-w"; A "-21"]);
        (* Do not load the ocaml core library and standard library *)
        flag ["ocaml"; "compile"] (S[A "-nopervasives"; A "-nostdlib"]);
        flag ["ocaml"; "link"] (S[A "-nopervasives"; A "-nostdlib"]);
    | _ ->
        ()
  )
