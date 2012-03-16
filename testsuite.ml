open Driver
open Types
open Expressions
open TypeChecker
open TestUtils

let check env point t =
  ignore (check_return_type env point t)

let tests = [
  ("arithmetic.hml", fun do_it ->
    let { type_env = env; _ } = do_it () in
    let int = find_type_by_name env "int" in
    let foo = point_by_name env "foo" in
    let bar = point_by_name env "bar" in
    check env foo int;
    check env bar int);

  ("list.hml", fun do_it ->
    let { type_env = env; _ } = do_it () in
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
  let path_to_pervasives = Driver.find_in_include_dirs "pervasives.hml" in
  let state = Driver.process Driver.empty_state path_to_pervasives in
  List.iter (fun (file, test) ->
    let do_it = fun () ->
      let state = Driver.process_raw state (Filename.concat "tests" file) in
      state
    in
    try
      test do_it;
      Printf.printf "%s✓ OH YEY %s%s\n" colors.green colors.default file
    with _ ->
      Printf.printf "%s✗ OH NOES %s%s\n" colors.red colors.default file;
      Printexc.print_backtrace stdout;
  ) tests
