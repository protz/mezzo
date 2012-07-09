open Types
open TypeChecker
open TestUtils

let check env point t =
  ignore (check_return_type env point t)

type outcome = Fail | Pass

let simple_test outcome f = fun do_it ->
  try
    ignore (do_it true);
    match outcome with Fail -> raise (Failure "") | Pass -> ();
  with TypeCheckerError e ->
    match e with
    | _, e when f e ->
        ()
    | _ ->
        raise (Failure "")

let tests = [
  ("constructors.hml",
    simple_test Pass (fun _ -> false));

  ("constructors_bad_1.hml",
    simple_test Fail (function MissingField _ -> true | _ -> false));

  ("constructors_bad_2.hml",
    simple_test Fail (function ExtraField _ -> true | _ -> false));

  ("field_access.hml",
    simple_test Pass (fun _ -> false));

  ("field_access_bad.hml",
    simple_test Fail (function NoSuchField _ -> true | _ -> false));

  ("field_assignment.hml",
    simple_test Pass (fun _ -> false));

  ("field_assignment_bad.hml",
    simple_test Fail (function NoSuchField _ -> true | _ -> false));

  ("arithmetic.hml", fun do_it ->
    let env = do_it true in
    let int = find_type_by_name env "int" in
    let foo = point_by_name env "foo" in
    let bar = point_by_name env "bar" in
    check env foo int;
    check env bar int);

  ("wrong_type_annotation.hml",
    simple_test Fail (function ExpectedType _ -> true | _ -> false));

  ("constraints_in_patterns.hml",
    simple_test Fail (function ExpectedType _ -> true | _ -> false));

  ("function.hml", fun do_it ->
    let env = do_it true in
    let int = find_type_by_name env "int" in
    let foobar = point_by_name env "foobar" in
    check env foobar (tuple [int; int]));

  ("list-length.hml", fun do_it ->
    let env = do_it false in
    let int = find_type_by_name env "int" in
    let zero = point_by_name env "zero" in
    check env zero int);

  ("list-concat.hml", fun do_it ->
    let env = do_it false in
    let x = point_by_name env "x" in
    let list = find_type_by_name env "list" in
    let t = TyForall ((Variable.register "foo", KType),
      TyApp (list, TyVar 0)
    ) in
    check env x t);

  ("list-map1.hml", fun do_it ->
    ignore (do_it false));

  ("stupid_match.hml",
    simple_test Fail (function NotNominal _ -> true | _ -> false));

  ("value_restriction.hml",
    simple_test Fail (function NoSuchField _ -> true | _ -> false));

  ("merge1.hml", fun do_it ->
    let env = do_it false in
    let v1 = point_by_name env "v1" in
    check env v1 (TyConcreteUnfolded (Datacon.register "T", [])));

  ("merge2.hml", fun do_it ->
    let env = do_it false in
    let v2 = point_by_name env "v2" in
    let t = TyExists ((Variable.register "foo", KTerm),
      TyBar (
        ty_equals v2,
        TyStar (
          TyAnchoredPermission (TyPoint v2,
            TyConcreteUnfolded (Datacon.register "U",
              [FieldValue (Field.register "left", TySingleton (TyVar 0));
               FieldValue (Field.register "right", TySingleton (TyVar 0))])),
          TyAnchoredPermission (
            TyVar 0,
            TyConcreteUnfolded (Datacon.register "T", [])
          )
        )
      ))
    in
    check env v2 t);

  ("merge3.hml", fun do_it ->
    let env = do_it false in
    let v3 = point_by_name env "v3" in
    let t = TyExists ((Variable.register "foo", KTerm),
      TyExists ((Variable.register "bar", KTerm),
        TyBar (
          ty_equals v3,
          fold_star [
            TyAnchoredPermission (TyPoint v3,
              TyConcreteUnfolded (Datacon.register "U",
                [FieldValue (Field.register "left", TySingleton (TyVar 0));
                 FieldValue (Field.register "right", TySingleton (TyVar 1))]));
            TyAnchoredPermission (
              TyVar 0,
              TyConcreteUnfolded (Datacon.register "T", [])
            );
            TyAnchoredPermission (
              TyVar 1,
              TyConcreteUnfolded (Datacon.register "T", [])
            );
          ]
        )))
    in
    check env v3 t);

  ("merge4.hml", fun do_it ->
    let env = do_it false in
    let v4 = point_by_name env "v4" in
    let w = find_type_by_name env "w" in
    let int = find_type_by_name env "int" in
    let t = TyApp (w, int) in
    check env v4 t);

  ("merge5.hml", fun do_it ->
    let env = do_it false in
    let v5 = point_by_name env "v5" in
    let v = find_type_by_name env "v" in
    let int = find_type_by_name env "int" in
    let t = TyApp (TyApp (v, int), int) in
    check env v5 t);

  ("merge6.hml", fun do_it ->
    let env = do_it false in
    let v6 = point_by_name env "v6" in
    let v = find_type_by_name env "v" in
    let int = find_type_by_name env "int" in
    let t = TyForall ((Variable.register "foo", KType),
      TyApp (TyApp (v, int), TyVar 0)
    )
    in
    check env v6 t);

  ("merge7.hml", fun do_it ->
    let env = do_it false in
    let v7 = point_by_name env "v7" in
    let v = find_type_by_name env "v" in
    let t = TyForall ((Variable.register "foo", KType),
      TyForall ((Variable.register "bar", KType),
        TyApp (TyApp (v, TyVar 1), TyVar 0)
      ))
    in
    check env v7 t);

  ("merge8.hml", fun do_it ->
    let env = do_it false in
    let v8 = point_by_name env "v8" in
    let v = find_type_by_name env "v" in
    let t = TyForall ((Variable.register "foo", KType),
        TyApp (TyApp (v, TyVar 0), TyVar 0)
      )
    in
    check env v8 t);

  ("merge_generalize_val.hml", fun do_it ->
    let env = do_it false in
    let x = point_by_name env "x" in
    let y = point_by_name env "y" in
    let z = point_by_name env "z" in
    let u = find_type_by_name env "u" in
    let t = TyForall ((Variable.register "foo", KType), TyApp (u, TyVar 0)) in
    check env x t;
    check env y t;
    check env z t;
  );

 ]

let _ =
  let open Bash in
  Log.enable_debug 0;
  Driver.add_include_dir "tests";
  List.iter (fun (file, test) ->
    let do_it = fun pervasives ->
      let env = Driver.process pervasives (Filename.concat "tests" file) in
      env
    in
    begin try
      test do_it;
      Printf.printf "%s✓ OH YEY %s%s\n" colors.green colors.default file;
    with e ->
      Printf.printf "%s✗ OH NOES %s%s\n" colors.red colors.default file;
      print_endline (Printexc.to_string e);
      Printexc.print_backtrace stdout;
    end;
    flush stdout;
    flush stderr;
  ) tests
