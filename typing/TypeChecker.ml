open Types
open Expressions

(* [has_flexible env t] checks [t] for flexible variables. *)
let has_flexible env t =
  let rec has_flexible t =
    match t with
    | TyUnknown
    | TyDynamic
    | TyVar _ ->
        false

    | TyPoint p ->
        if is_flexible env p then
          true
        else
          begin match structure env p with
          | Some t ->
              has_flexible t
          | None ->
              false
          end

    | TyForall (_, t)
    | TyExists (_, t) ->
        has_flexible t

    | TyArrow (t1, t2)
    | TyApp (t1, t2) ->
        has_flexible t1 || has_flexible t2

    | TyTuple components ->
        let components = List.map (function
          | TyTupleComponentValue t
          | TyTupleComponentPermission t ->
              has_flexible t
        ) components in
        List.exists (fun x -> x) components

    | TyConcreteUnfolded (_, fields) ->
        let fields = List.map (function
          | FieldValue (_, t)
          | FieldPermission t ->
              has_flexible t
        ) fields in
        List.exists (fun x -> x) fields

    | TySingleton t ->
        has_flexible t

    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        has_flexible t1 || has_flexible t2

    | TyEmpty ->
        false

  in
  has_flexible t
;;

(* Since everything is, or will be, in A-normal form, type-checking a function
 * call amounts to type-checking a point applied to another point. The default
 * behavior is: do not return a type that contains flexible variables. *)
let check_function_call (env: env) ?(allow_flexible: unit option) (f: point) (x: point): env * typ =
  let fname, fbinder = find_term env f in
  (* Find a suitable permission for [f] first *)
  let rec is_quantified_arrow = function
    | TyForall (_, t) ->
        is_quantified_arrow t
    | TyArrow _ ->
        true
    | _ ->
        false
  in
  let permissions = List.filter is_quantified_arrow fbinder.permissions in
  (* Instantiate all universally quantified variables with flexible variables. *)
  let rec flex = fun env -> function
    | TyForall (binding, t) ->
        let env, t = bind_var_in_type env ~flexible:true binding t in
        let env, t = flex env t in
        env, t
    | _ as t ->
        env, t
  in
  (* Instantiate flexible variables and deconstruct the resulting arrow. *)
  let flex_deconstruct t =
    match flex env t with
    | env, TyArrow (t1,t2) ->
        env, (t1, t2)
    | _ ->
        assert false
  in
  (* Try to give some useful error messages in case we have found not enough or
   * too many suitable types for [f]. *)
  let env, (t1, t2) =
    match permissions with
    | [] ->
        let open TypePrinter in
        Log.error "%a is not a function, the only permissions available for it are %a"
          Variable.p fname
          pdoc (print_permission_list, (env, fbinder))
    | t :: [] ->
        flex_deconstruct t
    | t :: _ ->
        Log.debug "More than one permission available for %a, strange"
          Variable.p fname;
        flex_deconstruct t
  in
  (* Examine [x]. *)
  let xname, xbinder = find_term env x in
  match Permissions.sub env x t1 with
  | Some env ->
      (* If we're not allowed to have flexible variables, make sure there aren't
       * any of them left hanging around. *)
      if not (Option.unit_bool allow_flexible) && has_flexible env t2 then begin
        let open TypePrinter in
        Log.error
          "The following type still contains flexible variables: %a"
          pdoc (ptype, (env, t2));
      end;
      (* Return the "good" type. *)
      env, t2
  | None ->
      let open TypePrinter in
      Log.error
        "Expected an argument of type %a but the only permissions available for %a are %a"
        pdoc (ptype, (env, t1)) Variable.p xname
        pdoc (print_permission_list, (env, xbinder))

;;


let rec check_expression (env: env) (expr: expression): env * point =
  match expr with
  | EPoint p ->
      env, p

  | _ ->
      assert false
;;
