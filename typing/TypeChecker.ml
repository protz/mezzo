open Types

(* Since everything is, or will be, in A-normal form, type-checking a function
 * call amounts to type-checking a point applied to another point. *)
let check_function_call (env: env) (f: point) (x: point): env * typ =
  let fname, fbinder = find_expr env f in
  (* Find a suitable permission for [f] first *)
  let permissions = List.filter (function TyArrow _ -> true | _ -> false) fbinder.permissions in
  let t1, t2 =
    match permissions with
    | [] ->
        let open TypePrinter in
        Log.error "%a is not a function, the only permissions available for it are %a"
          Variable.p fname
          pdoc (print_permission_list, (env, fbinder))
    | TyArrow (t1, t2) :: [] ->
        t1, t2
    | TyArrow (t1, t2) :: _ ->
        Log.debug "More than one permission available for %a, strange"
          Variable.p fname;
        t1, t2
    | _ ->
        assert false
  in
  (* Examine [x]. *)
  let xname, xbinder = find_expr env x in
  match Permissions.sub env x t1 with
  | Some env ->
      env, t2
  | None ->
      let open TypePrinter in
      Log.error
        "Expected an argument of type %a but the only permissions available for %a are %a"
        pdoc (ptype, (env, t1)) Variable.p xname
        pdoc (print_permission_list, (env, xbinder))

;;
