open TypeCore
open Types
open TestUtils
open Kind

let unit_tests = [
  (* A list of:
   * - a test name,
   * - a test,
   * - Some () (known failure) or None (works)
   * - the expected outcome. *)
  "levels", (begin fun () -> 
    let env = empty_env in
    let env, x = bind_rigid env (user "x" KTerm) in
    let env = Permissions.add env x (tuple []) in
    (* x @ () *)
    let env, f = bind_rigid env (user "f" KTerm) in
    let env = Permissions.add env f (forall ("c", KType) (unit @-> bar (TyBound 0) empty @-> unit)) in
    (* f @ [c] consumes () -> (c -> ()) *)
    let env, g = bind_rigid env (user "g" KTerm) in
    let env = Permissions.add env g ((forall ("a", KType) (forall ("b", KType) (
      tuple [TyBound 0; TyBound 1]
    )) @-> unit) @-> unit) in
    (* g @ (consumes g: {a, b} (a, b) -> ()) -> () *)
    let env, arg = bind_rigid env (user "arg" KTerm) in
    let env, t = TypeChecker.check_function_call env f x in
    let env = Permissions.add env arg t in
    let env, _ = TypeChecker.check_function_call env g arg in
    Log.debug "Flexible: %a\nResulting permissions: %a"
      internal_pflexlist env
      TypePrinter.ppermissions env
  end, None, Pass);

  "occurs-check", (begin fun () ->
    let env = empty_env in
    let env, x = bind_flexible env (user "x" KType) in
    let env =
      Permissions.instantiate_flexible env x (TyTuple [TyOpen x; TyOpen x])
    in
    ignore env
  end, Some (), Fail (fun _ -> true));

  "shortest", (begin fun () ->
    let env = Driver.process "tests/shortest.mz" in
    let buf = Buffer.create 2048 in
    Driver.print_signature buf env
  end, Some (), Pass);
];;

(* make tests/unit/UnitTests.byte *)
(* let _ =
  Log.enable_debug 8;
  List.iter (fun (_, (f, _, _)) ->
    f ()
  ) unit_tests *)
