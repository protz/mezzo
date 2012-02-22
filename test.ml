(*
val add_perm: working_env -> typ -> working_env (* performs the merge operation *)
val unfold_perm_one_round: general_env -> typ -> typ
val substract_perm: working_env -> typ -> working_env
val collect_flexible: typ -> typ
*)

open Types

let point_for_data_type (env: env) (name: string): point =
  let module T = struct exception Found of point end in
  try
    fold_types env (fun () point names _binding ->
      if Variable.print (List.hd names) = name then
        raise (T.Found point)) ();
    raise Not_found
  with T.Found point ->
    point
;;

let find_point env name =
  TyPoint (point_for_data_type env name)
;;

let parse_and_build_types () =
  let ast, _decls = Driver.lex_and_parse "tests/testperm.hml" in
  let env = WellKindedness.(check_data_type_group empty ast) in
  Log.debug ~level:4 "%a\n" TypePrinter.pdoc (WellKindedness.KindPrinter.print_kinds, env);
  let env = FactInference.analyze_data_types env in
  env
;;

let print_env (env: env) =
  let open TypePrinter in
  Log.debug ~level:1 "%a\n" pdoc (print_permissions, env);
;;

let test_adding_perms (env: env) =
  (* Since these are global names, they won't change, so we can fetch them right
   * now. *)
  let int = find_point env "int" in
  let t1 = find_point env "t1" in
  let ref = find_point env "ref" in
  (* First binding. *)
  let env, foo = bind_expr env (Variable.register "foo") in
  print_env env;
  (* We add: [foo: ref int] *)
  let env = Permissions.raw_add env foo (TyApp (ref, int)) in
  (* We add: [foo: t1 (ref int)] *)
  let env = Permissions.raw_add env foo (TyApp (t1, TyApp (ref, int))) in
  print_env env;
  (* Second binding. *)
  let env, bar = bind_expr env (Variable.register "bar") in
  (* We add: [bar: t1 int] *)
  let env = Permissions.raw_add env bar (TyApp (t1, int)) in
  let env = Permissions.raw_add env foo (TyApp (t1, int)) in
  (* Let's see what happens now. *)
  print_env env;
  (* Third binding. *)
  let env, _baz = bind_expr env (Variable.register "baz") in
  (* Log.debug "%a\n" TypePrinter.pdoc (TypePrinter.print_binders, env); *)
  print_env env;
;;

let test_expansion (env: env) =
  let env, foo = bind_expr env (Variable.register "foo") in
  let list x = TyApp (find_point env "list", x) in
  let t1 x = TyApp (find_point env "t1", x) in
  let int = find_point env "int" in
  let cons (head, tail) =
    TyConcreteUnfolded (Datacon.register "Cons",
      [FieldValue (Field.register "head", head);
       FieldValue (Field.register "tail", tail)])
  in
  let nil =
    TyConcreteUnfolded (Datacon.register "Nil", [])
  in
  let points_to x = TySingleton (TyPoint x) in
  let t = cons (int, list int) in
  let env = Permissions.add env foo t in
  print_env env;
  let env, bar = bind_expr env (Variable.register "bar") in
  let env = Permissions.add env bar (t1 nil) in
  let env, baz = bind_expr env (Variable.register "baz") in
  let env = Permissions.add env baz (t1 (points_to foo)) in
  print_env env;
;;

let _ =
  let open TypePrinter in
  Log.enable_debug 3;
  let env = parse_and_build_types () in
  (* Check that the kinds and facts we've built are correct. *)
  Log.debug ~level:1 "%a"
    Types.TypePrinter.pdoc (WellKindedness.KindPrinter.print_kinds_and_facts, env);
  flush stderr;
  print_newline ();
  (* Test various features. *)
  test_adding_perms env;
  test_expansion env;
;;
