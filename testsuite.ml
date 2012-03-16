open Driver
open Types
open Expressions
open TypeChecker
open TestUtils

let check env point t =
  ignore (check_return_type env point t)

let tests = [
  ("arithmetic.hml", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env "int" in
    let foo = point_by_name env "foo" in
    let bar = point_by_name env "bar" in
    check env foo int;
    check env bar int);

  ("list.hml", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env "int" in
    let zero = point_by_name env "zero" in
    check env zero int);

  ("constraints_in_patterns.hml", fun do_it ->
    try
      ignore (do_it ());
      raise (Failure "")
    with TypeCheckerError e ->
      match e with
      | env, ExpectedType (t, _, _) ->
          let int = find_type_by_name env "int" in
          let xlist x =
            let c = find_type_by_name env "xlist" in
            TyApp (c, x)
          in
          assert (equal env t (xlist int))
      | _ ->
          raise (Failure ""));

  ("wrong_type_annotation.hml", fun do_it ->
    try
      ignore (do_it ());
      raise (Failure "")
    with TypeCheckerError e ->
      match e with
      | env, ExpectedType (t, _, _) ->
          let int = find_type_by_name env "int" in
          assert (equal env t (int @-> int))
      | _ ->
          raise (Failure ""));

  ("value_restriction.hml", fun do_it ->
    try
      ignore (do_it ());
      raise (Failure "")
    with TypeCheckerError e ->
      match e with
      | env, ExpectedType (_, _, r) ->
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
      let env = Driver.process (Filename.concat "tests" file) in
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
