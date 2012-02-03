(*
- Ajouter TyAbstract, TyFlexible... ?
val add_perm: working_env -> typ -> working_env
val unfold_perm_one_round: general_env -> typ -> typ
val
*)

let _ =
  Log.enable_debug ();
  let ast, _decls = Driver.lex_and_parse "tests/testperm.hml" in
  let kenv = WellKindedness.(check_data_type_group empty ast) in
  let facts = FactInference.analyze_data_types kenv in
  let env = Env.create kenv facts in
  ignore (env, facts, kenv, ast);
