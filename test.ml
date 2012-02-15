(*
val add_perm: working_env -> typ -> working_env (* performs the merge operation *)
val unfold_perm_one_round: general_env -> typ -> typ
val substract_perm: working_env -> typ -> working_env
val collect_flexible: typ -> typ
*)

open Types

let index_for_data_type (env: env) (name: string): index =
  let module T = struct exception Found of index end in
  try
    ByIndex.iter_upi
      (fun index ->
        function
          | (tname, TypeBinding _) when Variable.print tname = name ->
            raise (T.Found index)
          | _ ->
            ()
      )
      env.bindings;
    raise Not_found
  with T.Found index ->
  index
;;

let parse_and_build_types () =
  let ast, _decls = Driver.lex_and_parse "tests/testperm.hml" in
  let env = WellKindedness.(check_data_type_group empty ast) in
  let env = FactInference.analyze_data_types env in
  env
;;

let print_env (env: env) =
  let open TypePrinter in
  Log.debug ~level:1 "%a\n" pdoc (print_permissions, env);
;;

let test_adding_perms (env: env) =
  (* Add two bindings in the environment *)
  let env = bind_expr env (Variable.register "foo") in
  let env = bind_expr env (Variable.register "bar") in
  (* Find the indices so that we can build the type ourselves. *)
  let t1 = TyVar (index_for_data_type env "t1") in
  let int = TyVar (index_for_data_type env "int") in
  let ref = TyVar (index_for_data_type env "ref") in
  (* We add: [bar: t1 int] *)
  let env = Permissions.raw_add env 0 (TyApp (t1, int)) in
  (* We add: [foo: ref int] *)
  let env = Permissions.raw_add env 1 (TyApp (ref, int)) in
  (* We add: [foo: ref (t1 int)] *)
  let env = Permissions.raw_add env 1 (TyApp (t1, TyApp (ref, int))) in
  (* Let's see what happens now. *)
  print_env env;
  (* This should ensure we properly lift the permissions when we call
   * permissions_for_ident. *)
  let env = bind_expr env (Variable.register "baz") in
  (* Log.debug "%a\n" TypePrinter.pdoc (TypePrinter.print_binders, env); *)
  print_env env;
;;

let _ =
  let open TypePrinter in
  Log.enable_debug 2;
  let env = parse_and_build_types () in
  Log.debug ~level:1 "%a"
    Types.TypePrinter.pdoc (WellKindedness.KindPrinter.print_kinds_and_facts, env);
  (* The function above may output some debug information. *)
  flush stderr;
  print_newline ();
  (* This should print no permissions at all *)
  print_env env;
  (* Test [t1] and [ref]. *)
  test_adding_perms env;
;;
