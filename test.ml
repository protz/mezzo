(*
val add_perm: working_env -> typ -> working_env (* performs the merge operation *)
val unfold_perm_one_round: general_env -> typ -> typ
val substract_perm: working_env -> typ -> working_env
val collect_flexible: typ -> typ
*)

open Types
open Env

let level_for_data_type (working_env: working_env) (name: string): level =
  let module T = struct exception Found of level end in
  try
    LevelMap.iter
      (fun level the_name -> if name = the_name then raise (T.Found level))
      working_env.name_for_type;
    raise Not_found
  with T.Found level ->
    level
;;

let parse_and_build_types () =
  let ast, _decls = Driver.lex_and_parse "tests/testperm.hml" in
  let kenv = WellKindedness.(check_data_type_group empty ast) in
  let facts = FactInference.analyze_data_types kenv in
  let program_env, working_env = Env.create kenv facts in
  program_env, working_env
;;

let add_expr_binder (working_env: working_env) (name: string): working_env * level =
  (* Create a set of permissions for that new binder. *)
  let permissions = { duplicable = []; exclusive = [] } in
  let elevel = working_env.elevel in
  let point, state = PersistentUnionFind.create permissions working_env.state in 
  let point_of_ident = LevelMap.add elevel point working_env.point_of_ident in
  let name_for_expr = LevelMap.add elevel name working_env.name_for_expr in
  { working_env with
    point_of_ident;
    elevel = elevel + 1;
    state; name_for_expr
  }, elevel
;;

let print_env (working_env: working_env) =
  let open EnvPrinter in
  Log.debug "%a" pdoc (print_working_env, working_env);
;;

let test_adding_one_perm (program_env: program_env) (working_env: working_env) =
  let tyvar level: typ =
    TyVar (working_env.tlevel - level)
  in
  let t1 = tyvar (level_for_data_type working_env "t1") in
  let int = tyvar (level_for_data_type working_env "int") in
  let working_env, foobar = add_expr_binder working_env "foobar" in
  let working_env =
    Permissions.raw_add program_env working_env foobar (TyApp (t1, int))
  in
  print_env working_env;
;;

let _ =
  let open EnvPrinter in
  Log.enable_debug ();
  let program_env, working_env = parse_and_build_types () in
  (* The function above may output some debug information. *)
  flush stderr;
  print_newline ();
  (* This should print no permissions at all *)
  print_env working_env;
  (* Test [t1]. *)
  test_adding_one_perm program_env working_env;
;;
