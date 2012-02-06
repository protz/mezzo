(*
val add_perm: working_env -> typ -> working_env (* performs the merge operation *)
val unfold_perm_one_round: general_env -> typ -> typ
val substract_perm: working_env -> typ -> working_env
val collect_flexible: typ -> typ
*)

let _ =
  Log.enable_debug ();
  let ast, _decls = Driver.lex_and_parse "tests/testperm.hml" in
  let kenv = WellKindedness.(check_data_type_group empty ast) in
  let facts = FactInference.analyze_data_types kenv in
  let program_env, working_env = Env.create kenv facts in
  ignore (program_env, working_env, facts, kenv, ast);
