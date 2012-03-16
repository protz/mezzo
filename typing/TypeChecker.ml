open Types
open Expressions
open Utils

(* -------------------------------------------------------------------------- *)

(* Error handling *)

type error = env * raw_error

and raw_error =
  | NotAFunction of Variable.name * term_binder
  | HasFlexible of typ
  | ExpectedType of typ * Variable.name * term_binder
  | RecursiveOnlyForFunctions
  | MissingField of Field.name
  | ExtraField of Field.name
  | NoSuchField of point * Field.name
  | SubPattern of pattern

exception TypeCheckerError of error

let raise_error env e =
  raise (TypeCheckerError (env, e))
;;

let print_error buf (env, raw_error) =
  let open TypePrinter in
  let open WellKindedness.KindPrinter in
  let open ExprPrinter in
  match raw_error with
  | NotAFunction (fname, fbinder) ->
      Printf.bprintf buf
        "%a %a is not a function, the only permissions available for it are %a"
        Lexer.p env.position
        Variable.p fname
        pdoc (print_permission_list, (env, fbinder))
  | HasFlexible t ->
      Printf.bprintf buf
        "%a the following type still contains flexible variables: %a"
        Lexer.p env.position
        pdoc (ptype, (env, t));
  | ExpectedType (t1, xname, xbinder) ->
      Printf.bprintf buf
        "%a expected an argument of type %a but the only permissions available for %a are %a"
        Lexer.p env.position
        pdoc (ptype, (env, t1)) Variable.p xname
        pdoc (print_permission_list, (env, xbinder))
  | RecursiveOnlyForFunctions ->
      Printf.bprintf buf
        "%a recursive definitions are enabled for functions only"
        Lexer.p env.position
  | MissingField f ->
      Printf.bprintf buf
        "%a field %a is missing in that constructor"
        Lexer.p env.position
        Field.p f
  | ExtraField f ->
      Printf.bprintf buf
        "%a field %a is superfluous in that constructor"
        Lexer.p env.position
        Field.p f
  | NoSuchField (point, f) ->
      let name, binder = find_term env point in
      Printf.bprintf buf
        "%a %a has no suitable permission with field %a, the only permissions \
          available for it are %a"
        Lexer.p env.position
        Variable.p name
        Field.p f
        pdoc (print_permission_list, (env, binder))
  | SubPattern pat ->
      Printf.bprintf buf
        "%a there's a sub-constraint in that pattern, not allowed: %a"
        Lexer.p env.position
        pdoc (ppat, (env, pat))
;;

(* -------------------------------------------------------------------------- *)

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
        raise_error env (NotAFunction (fname, fbinder))
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
        raise_error env (HasFlexible t2)
      end;
      (* Return the "good" type. *)
      env, t2
  | None ->
      raise_error env (ExpectedType (t1, xname, xbinder))

;;


let check_return_type (env: env) (point: point) (t: typ): env =
  match Permissions.sub env point t with
  | Some env ->
      env
  | None ->
      let open TypePrinter in
      let name, binder = find_term env point in
      Log.debug ~level:4 "%a\n------------\n" penv env;
      raise_error env (ExpectedType (t, name, binder))
;;


let type_for_function_def (expression: expression): typ =
  match expression with
  | EFun (vars, args, return_type, _) ->
      let t = List.fold_right (fun t acc -> TyArrow (t, acc)) args return_type in
      let t = List.fold_right (fun var acc -> TyForall (var, acc)) vars t in
      t
  | _ ->
      Log.error "[type_for_function_def], as the name implies, expects a \
        function expression...";
;;


let extract_constraint (env: env) (pattern: pattern): pattern =

  let rec extract_constraint (env: env) (pattern: pattern): pattern * typ =
    match pattern with
    | PConstraint (pattern, typ) ->
        let pattern, sub_typ = extract_constraint env pattern in
        begin match sub_typ with
        | TyUnknown ->
            pattern, typ
        | _ ->
            raise_error env (SubPattern pattern)
        end

    | PVar name ->
        PVar name, TyUnknown

    | PPoint point ->
        PPoint point, TyUnknown

    | PTuple pats ->
        let pats, ts = List.split (List.map (extract_constraint env) pats) in
        PTuple pats, TyTuple (List.map (fun x -> TyTupleComponentValue x) ts)

    | PConstruct (name, fieldpats) ->
        let fieldpats, fieldtypes = List.fold_left
          (fun (fieldpats, fieldtypes) (field, pat) ->
            let pat, t = extract_constraint env pat in
            (field, pat) :: fieldpats, (field, t) :: fieldtypes)
          ([], []) fieldpats
        in
        let fieldtypes = List.map (fun x -> FieldValue x) fieldtypes in
        PConstruct (name, fieldpats), TyConcreteUnfolded (name, fieldtypes)


    | PLocated (pattern, p1, p2) ->
        let pattern, typ = extract_constraint (locate env (p1, p2)) pattern in
        PLocated (pattern, p1, p2), typ
  in
  
  let pattern, t = extract_constraint env pattern in
  PConstraint (pattern, t)
;;


let rec unify_pattern (env: env) (pattern: pattern) (point: point): env =

  match pattern with
  | PConstraint (pattern, t) ->
      let env = check_return_type env point t in
      unify_pattern env pattern point

  | PVar _ ->
      Log.error "[unify_pattern] takes a pattern that has been run through \
        [subst_pat] first"

  | PPoint p ->
      (* [point] is the descriptor that has all the information; [p] just has
       * [=p] as a permission, and maybe an extra one if it's a [val rec f]
       * where [f] is a recursive function *)
      merge_left env point p

  | PTuple patterns ->
      let permissions = get_permissions env point in
      let t = List.map (function TyTuple x -> Some x | _ -> None) permissions in
      let t = Hml_List.filter_some t in
      Log.affirm (List.length t = 1) "Multiple candidates as a tuple type for \
        this pattern";
      let t = List.hd t in
      List.fold_left2 (fun env pattern component ->
        match component with
        | TyTupleComponentValue (TySingleton (TyPoint p')) ->
            unify_pattern env pattern p'
        | _ ->
            Log.error "Expecting a type that went through [unfold] and [collect] here"
      ) env patterns t

  | PConstruct (datacon, field_pats) ->
      let permissions = get_permissions env point in
      let field_defs = List.map
        (function
          | TyConcreteUnfolded (datacon', x) when Datacon.equal datacon datacon' ->
              Some x
          | _ ->
              None)
        permissions
      in
      let field_defs = Hml_List.filter_some field_defs in
      Log.affirm (List.length field_defs = 1) "Multiple candidates as a concrete type for \
        this pattern";
      let field_defs = List.hd field_defs in
      List.fold_left2 (fun env (name, pat) field ->
        match field with
        | FieldValue (name', TySingleton (TyPoint p')) ->
            Log.affirm (name = name') "I thought the fields were in the same order";
            unify_pattern env pat p'
        | _ ->
            Log.error "Expecting a type that went through [unfold] and [collect] here"
      ) env field_pats field_defs

  | PLocated (pat, p1, p2) ->
      let env = locate env (p1, p2) in
      unify_pattern env pat point

;;


let rec check_expression (env: env) ?(hint: string option) (expr: expression): env * point =

  (* TEMPORARY this is just a quick and dirty way to talk about user-defined
   * types. *)
  let int = find_type_by_name env "int" in

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
    let env, x1 = check_expression env ?hint:hint1 e1 in
    let env, x2 = check_expression env ?hint:hint2 e2 in
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

  | ELet (rec_flag, patexprs, body) ->
      let env, { subst_expr; _ } = check_bindings env rec_flag patexprs in
      let body = subst_expr body in
      check_expression env body


  (*| EFun of (Variable.name * kind) list * typ list * typ * expression*)

  | EAssign (e1, fname, e2) ->
      let hint = Option.map (fun x -> Printf.sprintf "%s_%s" x (Field.print fname)) hint in
      let env, p1 = check_expression env ?hint e1 in
      let env, p2 = check_expression env e2 in
      let env = replace_term env p1 (fun binder ->
        let permissions = binder.permissions in
        let found = ref false in
        let permissions = List.map (fun t ->
            match t with
            | TyConcreteUnfolded (datacon, fieldexprs) ->
                let fieldexprs = List.map (function
                  | FieldValue (field, expr) ->
                      let expr = 
                        if Field.equal field fname then
                          begin match expr with
                          | TySingleton (TyPoint _) ->
                              if !found then
                                Log.error "Two matching permissions? That's strange...";
                              found := true;
                              TySingleton (TyPoint p2)
                          | t ->
                              let open TypePrinter in
                              Log.error "Not a point %a" pdoc (ptype, (env, t))
                          end
                        else
                          expr
                      in
                      FieldValue (field, expr)
                  | FieldPermission _ as f ->
                      f
                ) fieldexprs in
                TyConcreteUnfolded (datacon, fieldexprs)
            | _ ->
                t
          ) permissions
        in
        { binder with permissions })
      in
      return env ty_unit

  | EAccess (e, fname) ->
      let hint = Option.map (fun x -> Printf.sprintf "%s_%s" x (Field.print fname)) hint in
      let env, p = check_expression env ?hint e in
      let module M = struct exception Found of point end in
      begin try
        List.iter (fun t ->
          match t with
          | TyConcreteUnfolded (_, fieldexprs) ->
              List.iter (function
                | FieldValue (field, expr) ->
                    if Field.equal field fname then
                      begin match expr with
                      | TySingleton (TyPoint p) ->
                          raise (M.Found p)
                      | t ->
                          let open TypePrinter in
                          Log.error "Not a point %a" pdoc (ptype, (env, t))
                      end;
                | FieldPermission _ ->
                    ()
              ) fieldexprs
          | _ ->
              ()
        ) (get_permissions env p);
        raise_error env (NoSuchField (p, fname))
      with M.Found p' ->
        env, p'
      end

  | EApply (e1, e2) ->
      let hint1 = Option.map (fun x -> x ^ "_fun") hint in
      let hint2 = Option.map (fun x -> x ^ "_arg") hint in
      let env, x1 = check_expression env ?hint:hint1 e1 in
      let env, x2 = check_expression env ?hint:hint2 e2 in
      let env, return_type = check_function_call env x1 x2 in
      return env return_type

  (* | EMatch of expression * (pattern * expression) list *)

  | ETuple exprs ->
      let env, components = Hml_List.fold_lefti
        (fun i (env, components) expr ->
          let hint = Option.map (fun x -> Printf.sprintf "%s_%d" x i) hint in
          let env, p = check_expression env ?hint expr in
          env, TyTupleComponentValue (ty_equals p) :: components)
        (env, []) exprs
      in
      let components = List.rev components in
      return env (TyTuple components)

  | EConstruct (datacon, fieldexprs) ->
      (* Find the corresponding definition. *)
      let _flag, branches = def_for_datacon env datacon in
      (* And the corresponding branch, so that we obtain the field names in order. *)
      let branch =
        List.find (fun (datacon', _) -> Datacon.equal datacon datacon') branches
      in
      (* Take out of the provided fields one of them. *)
      let take env name' l =
        try
          let elt = List.find (fun (name, _) -> Field.equal name name') l in
          snd elt, List.filter (fun x -> x != elt) l
        with Not_found ->
          raise_error env (MissingField name')
      in
      (* Do the bulk of the work. *)
      let env, remaining, fieldvals = List.fold_left (fun (env, remaining, fieldvals) -> function
        | FieldValue (name, _t) ->
            (* Actually we don't care about the expected type for the field. We
             * just want to make sure all fields are provided. *)
            let e, remaining = take env name remaining in
            let hint = Option.map (fun hint -> hint ^ "_" ^ Field.print name) hint in
            let env, p = check_expression env ?hint e in
            env, remaining, FieldValue (name, ty_equals p) :: fieldvals
        | FieldPermission _ ->
            env, remaining, fieldvals
      ) (env, fieldexprs, []) (snd branch) in
      (* Make sure the user hasn't written any superfluous fields. *)
      begin match remaining with
      | (name, _) :: _ ->
          raise_error env (ExtraField name)
      | _ ->
          ()
      end;
      let fieldvals = List.rev fieldvals in
      return env (TyConcreteUnfolded (datacon, fieldvals))


  (* | EIfThenElse of expression * expression * expression *)

  | EInt _ ->
      return env int

  | EUMinus e ->
      let hint = Option.map (fun x -> "-" ^ x) hint in
      let env, x = check_expression env ?hint e in
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
      Log.error "Not implemented yet!"


and check_bindings
  (env: env)
  (rec_flag: rec_flag)
  (patexprs: (pattern * expression) list): env * substitution_kit
  =
    let env, patexprs, subst_kit = bind_patexprs env rec_flag patexprs in
    let { subst_expr; subst_pat; _ } = subst_kit in
    let patterns, expressions = List.split patexprs in
    let expressions = List.map subst_expr expressions in
    let patterns = List.map subst_pat patterns in
    let env = match rec_flag with
      | Recursive ->
          List.fold_left2 (fun env expr pat ->
            let pat = punloc pat in
            let expr = eunloc expr in
            match pat, expr with
            | PPoint p, EFun _ ->
                Permissions.add env p (type_for_function_def expr)
            | _ ->
                raise_error env RecursiveOnlyForFunctions
          ) env expressions patterns
      | Nonrecursive ->
          env
    in
    let env = List.fold_left2 (fun env pat expr ->
      let hint = match pat with
        | PLocated ((PPoint p), _, _) ->
            Some (Variable.print (get_name env p))
        | _ ->
            None
      in
      let env, point = check_expression env ?hint expr in
      let pat = extract_constraint env pat in
      let env = unify_pattern env pat point in
      env) env patterns expressions
    in
    env, subst_kit
;;

let rec check_declaration_group (env: env) (declarations: declaration_group): env =
  match declarations with
  | DLocated (declarations, p1, p2) :: tl ->
      let env = locate env (p1, p2) in
      check_declaration_group env (declarations :: tl)
  | DMultiple (rec_flag, patexprs) :: tl ->
      let env, { subst_decl; _ } = check_bindings env rec_flag patexprs in
      let tl = subst_decl tl in
      check_declaration_group env tl
  | [] ->
      env
;;
