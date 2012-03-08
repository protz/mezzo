open Types
(* Some test helpers to easily build types by hand. *)

let parse_and_build_types () =
  let program = Driver.lex_and_parse "tests/testperm.hml" in
  let env, _declarations = WellKindedness.check_program program in
  Log.debug ~level:4 "%a\n" TypePrinter.pdoc (WellKindedness.KindPrinter.print_kinds, env);
  let env = FactInference.analyze_data_types env in
  env
;;

let print_env (env: env) =
  let open TypePrinter in
  Log.debug ~level:1 "%a\n" pdoc (print_permissions, env);
;;

(* ------------------------------------------------------------------------- *)

(* Some test helpers to easily build types by hand. *)

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

(* Some OCaml functions that create HaMLeT types. *)

let cons (head, tail) =
  TyConcreteUnfolded (Datacon.register "Cons",
    [FieldValue (Field.register "head", head);
     FieldValue (Field.register "tail", tail)])
;;

let nil =
  TyConcreteUnfolded (Datacon.register "Nil", [])
;;

let tuple l =
  TyTuple (List.map (function
    | TyEmpty as p
    | (TyStar _ as p)
    | (TyAnchoredPermission _ as p) ->
        TyTupleComponentPermission p
    | x ->
        TyTupleComponentValue x) l)
;;

let point x =
  TyPoint x
;;

let points_to x =
  TySingleton (point x)
;;

let permission (p, x) =
  TyAnchoredPermission (p, x)
;;

let forall (x, k) t =
  TyForall ((Variable.register x, k), t)
;;

let var x =
  TyVar x
;;

(* This is right-associative, so you can write [list int @-> int @-> tuple []] *)
let (@->) x y =
  TyArrow (x, y)
;;

let ktype =
  SurfaceSyntax.KType
;;

let unit =
  tuple []
;;

(* Green ☑ checkmark (for the debug output). *)

let check = Bash.(Hml_String.bsprintf "%s✓%s" colors.green colors.default);;

(* ------------------------------------------------------------------------- *)

(* Various test points. The output is a bit messy right now, and there's very
 * few assertions for the correctness of the results.
 *
 * TODO: make sure [Permissions], [TypeChecker] and others fail in a meaningful
 * way (that is, by throwing a specific exception depending on the error), so
 * that we can assert that they failed "the right way". We should also write
 * some test helpers that assert that a given permission is present or not in
 * the environment, to ensure that everything goes "as expected". *)

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
  let env = Permissions.add env foo (TyApp (ref, int)) in
  (* We add: [foo: t1 (ref int)] *)
  let env = Permissions.add env foo (TyApp (t1, TyApp (ref, int))) in
  print_env env;
  (* Second binding. *)
  let env, bar = bind_expr env (Variable.register "bar") in
  (* We add: [bar: t1 int] *)
  let env = Permissions.add env bar (TyApp (t1, int)) in
  let env = Permissions.add env foo (TyApp (t1, int)) in
  (* Let's see what happens now. *)
  print_env env;
  (* Third binding. *)
  let env, _baz = bind_expr env (Variable.register "baz") in
  (* Log.debug "%a\n" TypePrinter.pdoc (TypePrinter.print_binders, env); *)
  print_env env;
;;

let test_unfolding (env: env) =
  (* Some wrappers for easily building types by hand. *)
  let list x = TyApp (find_point env "list", x) in
  let t1 x = TyApp (find_point env "t1", x) in
  let int = find_point env "int" in
  (* Make sure the unfolding is properly performed. *)
  let env, foo = bind_expr env (Variable.register "foo") in
  let t = cons (int, list int) in
  let env = Permissions.add env foo t in
  print_env env;
  (* Make sure data types with one branch are unfolded. *)
  let env, bar = bind_expr env (Variable.register "bar") in
  let env = Permissions.add env bar (t1 nil) in
  (* Make sure we don't introduce extra indirections when the field is already a
   * singleton. *)
  let env, baz = bind_expr env (Variable.register "baz") in
  let env = Permissions.add env baz (t1 (points_to foo)) in
  print_env env;
  (* Make sure the mechanism works for tuples as well. *)
  let env, toto = bind_expr env (Variable.register "toto") in
  let env = Permissions.add env toto (tuple [int; list int; points_to toto]) in
  print_env env;
  (* The two lines below throw [Permissions] into an infinite loop. Making sure
   * we don't loop is non-trivial, see notes from 2012/02/23. *)
  (* let loop x = TyApp ( env "loop", x) in
  let env, ananas = bind_expr env (Variable.register "ananas") in
  let env = Permissions.add env ananas (loop int) in
  print_env env; *)
;;

let test_refinement (env: env) =
  (* Some wrappers for easily building types by hand. *)
  let pair (x, y) = TyApp (TyApp (find_point env "pair", x), y) in
  let list x = TyApp (find_point env "list", x) in
  let ref x = TyApp (find_point env "ref", x) in
  let int = find_point env "int" in
  (* Make sure the unfolding is properly performed. *)
  let env, foo = bind_expr env (Variable.register "foo") in
  let env = match Permissions.refine_type env nil (list int) with
    | env, Permissions.One t ->
        Permissions.add env foo t
    | _, Permissions.Both ->
        Log.error "This permissions should be refined into just one"
  in
  print_env env;
  (* This should print out that an inconsistency was detected. *)
  let env, unreachable = bind_expr env (Variable.register "unreachable") in
  let t = ref int and t' = ref (ref int) in
  let env = match Permissions.refine_type env t t' with
    | env, Permissions.Both ->
        let env = Permissions.add env unreachable t in
        let env = Permissions.add env unreachable t' in
        env
    | _, Permissions.One _ ->
        Log.error "These two permissions are mutually exclusive"
  in
  print_env env;
  (* More elaborate. *)
  let env, bar = bind_expr env (Variable.register "bar") in
  let env, l = bind_expr env (Variable.register "l") in
  let env, r = bind_expr env (Variable.register "r") in
  let env = Permissions.add env bar (pair (points_to l, points_to r)) in
  print_env env;
  let env = Permissions.refine env bar (pair (int, int)) in
  let env = Permissions.refine env bar (pair (int, int)) in
  print_env env;
  let env = Permissions.unify env l r in
  print_env env;
  (* Moar elaborate. *)
  let env = Permissions.add env l (tuple [int; permission (point foo, int)]) in
  print_env env;
;;


let test_substraction (env: env) =
  (* Some wrappers for easily building types by hand. *)
  let list x = TyApp (find_point env "list", x) in
  let ref x = TyApp (find_point env "ref", x) in
  let int = find_point env "int" in
  (* Make sure the unfolding is properly performed. *)
  let env, foo = bind_expr env (Variable.register "foo") in
  let env = Permissions.add env foo (tuple [int; ref int]) in
  print_env env;
  let env = Option.extract (Permissions.sub env foo (tuple [int; ref int])) in
  (* The cool thing is, at that stage, the [ref int] permission has been removed
   * but the other ones are still valid. *)
  print_env env;
  (* We can't take that permission twice. *)
  assert (Permissions.sub env foo (tuple [int; ref int]) = None);
  let env, bar = bind_expr env (Variable.register "bar") in
  let env = Permissions.add env bar nil in
  (* This tests the "unfolded vs nominal" case. *)
  let env = Option.extract (Permissions.sub env bar (list int)) in
  let env = Option.extract (Permissions.sub env bar (list (ref int))) in
  print_env env;
;;

let test_function_call (env: env) =
  (* Some wrappers for easily building types by hand. *)
  let list x = TyApp (find_point env "list", x) in
  let ref x = TyApp (find_point env "ref", x) in
  let int = find_point env "int" in
  let _t1 x = TyApp (find_point env "t1", x) in
  (* Testing the function call *)
  (* Make sure the unfolding is properly performed. *)
  let env, length = bind_expr env (Variable.register "length") in
  let env, x = bind_expr env (Variable.register "x") in
  let env = Permissions.add env length
    (forall ("a", ktype) (list (var 0) @-> int))
  in
  let env = Permissions.add env x nil in
  let test_call env f x =
    Bash.(
      Log.debug "Testing with %s%s%s" colors.underline
        (Option.extract (name_for_expr env x)) colors.default);
    let env, t2 = TypeChecker.check_function_call env f x in
    TypePrinter.(
      Log.debug "%s Function call succeeded with type %a.\n\
                 Remaining permissions:\n"
        check pdoc (ptype, (env, t2)));
    print_env env;
    env
  in
  let env = test_call env length x in
  let env, y = bind_expr env (Variable.register "y") in
  let env = Permissions.add env y (list (ref int)) in
  let env = test_call env length y in
  let env, z = bind_expr env (Variable.register "z") in
  let env = Permissions.add env z (cons (ref int, list (ref int))) in
  let env = test_call env length z in

  (* Make sure these calls fail. *)
  try
    ignore (test_call env length z);
    Log.error "This call shouldn't be allowed; the permissions have been consumed already";
  with _ ->
    Log.debug "%s Test passed -- the error message above should be:\n   “\
      Expected an argument of type list a but the only permissions available \
      for z are Cons {…”" check;

  try
    let env, arg = bind_expr env (Variable.register "arg") in
    let env, newref = bind_expr env (Variable.register "newref") in
    let env = Permissions.add env newref (forall ("a", ktype) (tuple [] @-> (var 0))) in
    let env = Permissions.add env arg unit in
    ignore (test_call env newref arg);
    Log.error "This call shouldn't be allowed because there's flexible\
      variables in the return type"
  with _ ->
    Log.debug "%s Test passed -- the error message above should be:\n   “\
      The following type still contains flexible variables: a”" check;

  (* This one can't be expanded because it's abstract, tests a different
   * codepath (the one where the point is directly merged using [merge_left]). *)
  let env, deref = bind_expr env (Variable.register "deref") in
  let env = Permissions.add env deref (forall ("a", ktype) (ref (var 0) @-> (var 0))) in
  let env, arg = bind_expr env (Variable.register "arg") in
  let env = Permissions.add env arg (ref int) in
  let env = test_call env deref arg in

  ignore env;
;;

let _ =
  let open TypePrinter in
  Log.enable_debug 4;
  let env = parse_and_build_types () in
  (* Check that the kinds and facts we've built are correct. *)
  Log.debug ~level:1 "%a"
    Types.TypePrinter.pdoc (WellKindedness.KindPrinter.print_kinds_and_facts, env);
  flush stderr;
  print_newline ();
  (* Test various features. *)
  Printf.eprintf "%s" (Bash.box "Adding permissions");
  test_adding_perms env;
  Printf.eprintf "%s" (Bash.box "Unfolding permissions");
  test_unfolding env;
  Printf.eprintf "%s" (Bash.box "Refining permissions");
  test_refinement env;
  Printf.eprintf "%s" (Bash.box "Substracting permissions");
  test_substraction env;
  Printf.eprintf "%s" (Bash.box "Function call");
  test_function_call env;
;;
