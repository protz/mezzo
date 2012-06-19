open Types
open TypeChecker
open TestUtils

let check env point t =
  ignore (check_return_type env point t)

type outcome = Fail | Pass

let simple_test outcome f = fun do_it ->
  try
    ignore (do_it ());
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
    let env = do_it () in
    let int = find_type_by_name env "int" in
    let foo = point_by_name env "foo" in
    let bar = point_by_name env "bar" in
    check env foo int;
    check env bar int);

  ("wrong_type_annotation.hml",
    simple_test Fail (function ExpectedType _ -> true | _ -> false));

  ("constraints_in_patterns.hml", fun do_it ->
    try
      ignore (do_it ());
      raise (Failure "")
    with TypeCheckerError e ->
      match e with
      | env, ExpectedType (t, _) ->
          let int = find_type_by_name env "int" in
          let xlist x =
            let c = find_type_by_name env "xlist" in
            TyApp (c, x)
          in
          assert (equal env t (tuple [xlist int; xlist int]))
      | _ ->
          raise (Failure ""));

  ("function.hml", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env "int" in
    let foobar = point_by_name env "foobar" in
    check env foobar (tuple [int; int]));

  ("list.hml", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env "int" in
    let zero = point_by_name env "zero" in
    check env zero int);

  ("value_restriction.hml", fun do_it ->
    try
      ignore (do_it ());
      raise (Failure "")
    with TypeCheckerError e ->
      match e with
      | env, ExpectedType (_, p) ->
          let _, r = find_term env p in
          let p = point_by_name env "r" in
          let _, r' = find_term env p in
          assert (r = r')
      | _ ->
          raise (Failure ""));
]

let _ =
  let open Bash in
  Log.enable_debug 1;
  Driver.add_include_dir "tests";
  List.iter (fun (file, test) ->
    let do_it = fun () ->
      let env = Driver.process true (Filename.concat "tests" file) in
      env
    in
    try
      test do_it;
      Printf.printf "%s✓ OH YEY %s%s\n" colors.green colors.default file
    with e ->
      Printf.printf "%s✗ OH NOES %s%s\n" colors.red colors.default file;
      print_endline (Printexc.to_string e);
      Printexc.print_backtrace stdout;
  ) tests
