open Types
open Expressions
open Utils

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


let check_return_type (env: env) (point: point) (t: typ): env =
  match Permissions.sub env point t with
  | Some env ->
      env
  | None ->
      let open TypePrinter in
      let name, binder = find_term env point in
      Log.error "%a %a should have type %a but the only permissions available for it are %a"
        Lexer.p env.position
        Variable.p name
        pdoc (ptype, (env, t))
        pdoc (print_permission_list, (env, binder))
;;


let rec check_expression (env: env) ?(hint: string option) (expr: expression): env * point =

  (* TEMPORARY this is just a quick and dirty way to talk about user-defined
   * types. *)
  let int = Permissions.find_type_by_name env "int" in

  (* [return t] creates a new point with type [t] available for it, and returns
   * the environment as well as the point *)
  let return env t =
    (* Not the most clever function, but will do for now on *)
    let hint = Option.map_none (fresh_name "x_") hint in
    let env, x = bind_term env (Variable.register hint) false in
    let env = Permissions.add env x t in
    env, x
  in

  let check_arith_binop env e1 e2 op =
    let hint1 = Option.map (fun x -> Printf.sprintf "%s_%s_l" x op) hint in
    let hint2 = Option.map (fun x -> Printf.sprintf "%s_%s_r" x op) hint in
    let _env, x1 = check_expression env ?hint:hint1 e1 in
    let _env, x2 = check_expression env ?hint:hint2 e2 in
    let env = check_return_type env x1 int in
    let env = check_return_type env x2 int in
    return env int
  in

  match expr with
  | EConstraint (e, t) ->
      let env, p = check_expression env ?hint e in
      let env = check_return_type env p t in
      return env t

  | EVar _ ->
      Log.error "[check_expression] expects an expression where all variables \
        has been opened";

  | EPoint p ->
      env, p

  (*| ELet of rec_flag * (pattern * expression) list * expression

  | EFun of (Variable.name * kind) list * typ list * typ * expression

  | EAssign of expression * Field.name * expression

  | EAccess of expression * Field.name*)

  | EApply (e1, e2) ->
      let hint1 = Option.map (fun x -> x ^ "_fun") hint in
      let hint2 = Option.map (fun x -> x ^ "_arg") hint in
      let _env, x1 = check_expression env ?hint:hint1 e1 in
      let _env, x2 = check_expression env ?hint:hint2 e2 in
      let env, return_type = check_function_call env x1 x2 in
      return env return_type

  (* | EMatch of expression * (pattern * expression) list *)

  | ETuple exprs ->
      let types = Hml_List.mapi
        (fun i e ->
          let hint = Option.map (fun x -> Printf.sprintf "%s_%d" x i) hint in
          let _env, p = check_expression env ?hint e in
          TyTupleComponentValue (ty_equals p))
        exprs
      in
      return env (TyTuple types)

  (* | EConstruct of Datacon.name * (Field.name * expression) list

  | EIfThenElse of expression * expression * expression *)

  | EInt _ ->
      return env int

  | EUMinus e ->
      let hint = Option.map (fun x -> "-" ^ x) hint in
      let _env, x = check_expression env ?hint e in
      let env = check_return_type env x int in
      return env int

  | EPlus (e1, e2) ->
      check_arith_binop env e1 e2 "+"

  | EMinus (e1, e2) ->
      check_arith_binop env e1 e2 "-"

  | ETimes (e1, e2) ->
      check_arith_binop env e1 e2 "×"

  | EDiv (e1, e2) ->
      check_arith_binop env e1 e2 "/"

  | ELocated (e, p1, p2) ->
      let env = locate env (p1, p2) in
      check_expression env ?hint e

  | _ ->
      assert false
;;
