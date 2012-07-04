open Types
open Expressions
open Utils

(* -------------------------------------------------------------------------- *)

(* Error handling *)

type error = env * raw_error

and raw_error =
  | NotAFunction of point
  | HasFlexible of typ
  | ExpectedType of typ * point
  | RecursiveOnlyForFunctions
  | MissingField of Field.name
  | ExtraField of Field.name
  | NoSuchField of point * Field.name
  | NoSuchFieldInPattern of pattern * Field.name
  | SubPattern of pattern
  | NoTwoConstructors of point
  | NotNominal of point
  | MatchBadDatacon of typ * Datacon.name
  | MatchBadPattern of pattern
  | NoSuchPermission of typ
  | AssignNotExclusive of typ * Datacon.name

exception TypeCheckerError of error

let raise_error env e =
  raise (TypeCheckerError (env, e))
;;

let print_error buf (env, raw_error) =
  let open TypePrinter in
  let open ExprPrinter in
  let print_permissions () =
    Printf.bprintf buf "\nOH NOES. Printing permissions.\n\n%a" pdoc (print_permissions, env);
    Printf.bprintf buf "\nError message follows.\n\n";
  in
  match raw_error with
  | NotAFunction p ->
      let fname, fbinder = find_term env p in
      begin match Permissions.fold env p with
      | Some t ->
          Printf.bprintf buf
            "%a %a is not a function, it has type %a"
            Lexer.p env.position
            Variable.p fname
            ptype (env, t)
      | None ->
          print_permissions ();
          Printf.bprintf buf
            "%a %a is not a function, the only permissions available for it are %a"
            Lexer.p env.position
            Variable.p fname
            pdoc (print_permission_list, (env, fbinder))
      end
  | NoSuchPermission t ->
      Printf.bprintf buf
        "%a unable to extract the following permission: %a"
        Lexer.p env.position
        ptype (env, t);
   | HasFlexible t ->
      Printf.bprintf buf
        "%a the following type still contains flexible variables: %a"
        Lexer.p env.position
        ptype (env, t);
  | ExpectedType (t, point) ->
      let xname, xbinder = find_term env point in
      let t1 = Permissions.fold_type env t in
      let t2 = Permissions.fold env point in
      begin match t1, t2 with
      | Some t1, Some t2 -> (* #winning *)
           Printf.bprintf buf
            "%a expected a subexpression of type %a but it has type %a"
            Lexer.p env.position
            ptype (env, t1)
            ptype (env, t2)
      | _ ->
          print_permissions ();
          Printf.bprintf buf
            "%a expected an argument of type %a but the only permissions available for %a are %a"
            Lexer.p env.position
            ptype (env, t) Variable.p xname
            pdoc (print_permission_list, (env, xbinder))
      end
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
  | NotNominal point ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, we can't match on it"
            Lexer.p env.position
            Variable.p name
            ptype (env, t)
      | None ->
          print_permissions ();
          Printf.bprintf buf
            "%a %a has no permission with a nominal type suitable for matching, \
              the only permissions available for it are %a"
            Lexer.p env.position
            Variable.p name
            pdoc (print_permission_list, (env, binder))
      end
  | NoTwoConstructors point ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, is is not a type with two constructors"
            Lexer.p env.position
            Variable.p name
            ptype (env, t)
      | None ->
          print_permissions ();
          Printf.bprintf buf
            "%a %a has no suitable permission for a type with two constructors, \
              the only permissions available for it are %a"
            Lexer.p env.position
            Variable.p name
            pdoc (print_permission_list, (env, binder))
      end
  | NoSuchField (point, f) ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, which doesn't have a field named %a"
            Lexer.p env.position
            Variable.p name
            ptype (env, t)
            Field.p f
      | None ->
          print_permissions ();
          Printf.bprintf buf
            "%a %a has no suitable permission with field %a, the only permissions \
              available for it are %a"
            Lexer.p env.position
            Variable.p name
            Field.p f
            pdoc (print_permission_list, (env, binder))
      end
  | SubPattern pat ->
      Printf.bprintf buf
        "%a there's a sub-constraint in that pattern, not allowed: %a"
        Lexer.p env.position
        pdoc (ppat, (env, pat))
  | MatchBadDatacon (t, datacon) ->
      Printf.bprintf buf
        "%a matching on a value with type %a: it has no constructor named %a"
        Lexer.p env.position
        ptype (env, t)
        Datacon.p datacon
  | MatchBadPattern pat ->
      Printf.bprintf buf
        "%a the pattern %a is not valid inside a match; only matches on data \
          constructors are allowed"
        Lexer.p env.position
        pdoc (ppat, (env, pat))
  | NoSuchFieldInPattern (pat, field) ->
      Printf.bprintf buf
        "%a the pattern %a mentions field %a which is unknown for that branch"
        Lexer.p env.position
        pdoc (ppat, (env, pat))
        Field.p field
  | AssignNotExclusive (t, datacon) ->
      Printf.bprintf buf
        "%a this value has type %a: constructor %a belongs to a data type that \
          is not defined as exclusive"
        Lexer.p env.position
        ptype (env, t)
        Datacon.p datacon
;;

(* -------------------------------------------------------------------------- *)

let (!!) =
  Permissions.(!!)
;;

(* Since everything is, or will be, in A-normal form, type-checking a function
 * call amounts to type-checking a point applied to another point. The default
 * behavior is: do not return a type that contains flexible variables. *)
let check_function_call (env: env) (f: point) (x: point): env * typ =
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
        raise_error env (NotAFunction f)
    | t :: [] ->
        flex_deconstruct t
    | t :: _ ->
        Log.debug "More than one permission available for %a, strange"
          Variable.p fname;
        flex_deconstruct t
  in
  (* Examine [x]. [sub] will take care of running collect on [t1] so that the
   * expected permissions are subtracted as well from the environment. *)
  match Permissions.sub env x t1 with
  | Some env ->
      (* Return the "good" type. *)
      let t2, perms = Permissions.collect t2 in
      let env = List.fold_left Permissions.add_perm env perms in
      let t2 = Flexible.generalize env t2 in
      env, t2
  | None ->
      raise_error env (ExpectedType (t1, x))

;;


let check_return_type (env: env) (point: point) (t: typ): env =
  TypePrinter.(
    let _, binder = find_term env point in
    Log.debug ~level:4 "Expecting return type %a; permissions for the point: %a"
      ptype (env, t)
      pdoc (print_permission_list, (env, binder));
    (* TestUtils.print_env env ;*)
  );
    
  match Permissions.sub env point t with
  | Some env ->
      env
  | None ->
      let open TypePrinter in
      Log.debug ~level:4 "%a\n------------\n" penv env;
      raise_error env (ExpectedType (t, point))
;;


let type_for_function_def (expression: expression): typ =
  match expression with
  | EFun (vars, arg, return_type, _) ->
      let t = TyArrow (arg, return_type) in
      let t = List.fold_right (fun var acc -> TyForall (var, acc)) vars t in
      t
  | _ ->
      Log.error "[type_for_function_def], as the name implies, expects a \
        function expression...";
;;



let rec unify_pattern (env: env) (pattern: pattern) (point: point): env =

  match pattern with
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
      let t = Hml_List.map_some (function TyTuple x -> Some x | _ -> None) permissions in
      Log.check (List.length t = 1) "Multiple candidates as a tuple type for \
        this pattern";
      let t = List.hd t in
      List.fold_left2 (fun env pattern component ->
        match component with
        | TySingleton (TyPoint p') ->
            unify_pattern env pattern p'
        | _ ->
            Log.error "Expecting a type that went through [unfold] and [collect] here"
      ) env patterns t

  | PConstruct (datacon, field_pats) ->
      let permissions = get_permissions env point in
      let field_defs = Hml_List.map_some
        (function
          | TyConcreteUnfolded (datacon', x) when Datacon.equal datacon datacon' ->
              Some x
          | _ ->
              None)
        permissions
      in
      Log.check (List.length field_defs = 1) "Multiple candidates as a concrete type for \
        this pattern";
      let field_defs = List.hd field_defs in
      List.fold_left (fun env (name, pat) ->
        (* The pattern fields may not all be there or in an arbitrary order. *)
        let field =
          try
            List.find (function
              | FieldValue (name', _) when Field.equal name name' -> true
              | _ -> false) field_defs
          with Not_found ->
            raise_error env (NoSuchFieldInPattern (pattern, name))
        in
        match field with
        | FieldValue (_, TySingleton (TyPoint p')) ->
            unify_pattern env pat p'
        | _ ->
            Log.error "Expecting a type that went through [unfold] and [collect] here"
      ) env field_pats

;;


let rec check_expression (env: env) ?(hint: string option) (expr: expression): env * point =

  (* TEMPORARY this is just a quick and dirty way to talk about user-defined
   * types. This is lazy because we want to write simple test cases that do not
   * define the "int" type. *)
  let int = lazy (find_type_by_name env "int") in
  let (!*) = Lazy.force in

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
    let env = check_return_type env x1 !*int in
    let env = check_return_type env x2 !*int in
    return env !*int
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


  | EFun (vars, arg, return_type, body) ->
      (* We can't create a closure over exclusive variables. Create a stripped
       * environment with only the duplicable parts. *)
      let sub_env = fold_terms env (fun sub_env point _ _ ->
        replace_term sub_env point (fun raw ->
          let permissions =
            List.filter (FactInference.is_duplicable env) raw.permissions
          in
          { raw with permissions }
        )) env
      in

      (* Bind all variables. *)
      let sub_env, { subst_type; subst_expr; _ } = bind_vars sub_env vars in
      let arg = subst_type arg in
      let return_type = subst_type return_type in
      let body = subst_expr body in

      (* Collect all the permissions that the arguments bring into scope, add
       * them into the environment for checking the function body. *)
      let _, perms = Permissions.collect arg in
      let sub_env = List.fold_left Permissions.add_perm sub_env perms in

      (* Type-check the function body. *)
      let sub_env, p = check_expression sub_env body in

      begin match Permissions.sub sub_env p return_type with
      | Some _ ->
          (* Return the entire arrow type. *)
          let expected_type = type_for_function_def expr in
          return env expected_type
      | None ->
          raise_error sub_env (NoSuchPermission return_type)
      end

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
                (* Check that datacon points to a type that is defined as
                 * exclusive. *)
                let flag, _ = def_for_datacon env datacon in
                if flag <> SurfaceSyntax.Exclusive then
                  raise_error env (AssignNotExclusive (t, datacon));

                (* Perform the assignment. *)
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
                              Log.error "Not a point %a" ptype (env, t)
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
        if not !found then
          raise_error env (NoSuchField (p1, fname));
        { binder with permissions })
      in
      return env ty_unit

  | EAccess (e, fname) ->
      (* We could be a little bit smarter, and generic here. Instead of iterating
       * on the permissions, we could use a reverse map from field names to
       * types. We could then subtract the type (instanciated using flexible
       * variables) from the expression. In case the subtraction function does
       * something super fancy, like using P ∗ P -o τ to obtain τ, this would
       * allow us to reuse the code. Of course, this raises the question of
       * “what do we do in case there's an ambiguity”, that is, multiple
       * datacons that feature this field name... We'll leave that for later. *)
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
                          Log.error "Not a point %a" ptype (env, t)
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
      (* Give an error message that mentions the entire function call. We should
       * probably have a function called nearest_loc that returns the location
       * of [e2] so that we can be even more precise in the error message. *)
      let env, return_type = check_function_call env x1 x2 in
      return env return_type

  | ETuple exprs ->
      let env, components = Hml_List.fold_lefti
        (fun i (env, components) expr ->
          let hint = Option.map (fun x -> Printf.sprintf "%s_%d" x i) hint in
          let env, p = check_expression env ?hint expr in
          env, (ty_equals p) :: components)
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


  | EInt _ ->
      return env !*int

  | EUMinus e ->
      let hint = Option.map (fun x -> "-" ^ x) hint in
      let env, x = check_expression env ?hint e in
      let env = check_return_type env x !*int in
      return env !*int

  | EPlus (e1, e2) ->
      check_arith_binop env e1 e2 "+"

  | EMinus (e1, e2) ->
      check_arith_binop env e1 e2 "-"

  | ETimes (e1, e2) ->
      check_arith_binop env e1 e2 "×"

  | EDiv (e1, e2) ->
      check_arith_binop env e1 e2 "/"

  | ELocated (e, p1, p2) ->
      let pos = env.position in
      let env = locate env (p1, p2) in
      let env, p = check_expression env ?hint e in
      locate env pos, p

  | EIfThenElse (e1, e2, e3) ->
      let hint_1 = Option.map (fun x -> x ^ "-if") hint in
      let env, x1 = check_expression env ?hint:hint_1 e1 in
      
      (* The condition of an if-then-else statement is well-typed if it is a
       * data type with two branches. *)
      let is_data_type_with_two_constructors t =
        let has_two_branches p =
          if is_type env p then
            match get_definition env p with
            | Some (_, branches) ->
                List.length branches = 2
            | None ->
                false
          else
            false
        in
        match t with
        | TyPoint p ->
            (* e.g. bool *)
            has_two_branches p
        | TyApp _ ->
            (* e.g. list a *)
            let cons, _args = flatten_tyapp t in
            has_two_branches !!cons
        | TyConcreteUnfolded (datacon, _) ->
            (* e.g. False *)
            let _, branches = def_for_datacon env datacon in
            List.length branches = 2
        | _ ->
            false
      in

      if not (List.exists is_data_type_with_two_constructors (get_permissions env x1)) then
        raise_error env (NoTwoConstructors x1);

      (* The control-flow diverges. *)
      let hint_l = Option.map (fun x -> x ^ "-then") hint in
      let left = check_expression env ?hint:hint_l e2 in
      let hint_r = Option.map (fun x -> x ^ "-else") hint in
      let right = check_expression env ?hint:hint_r e3 in

      Merge.merge_envs env left right

  | EMatch (e, patexprs) ->
      (* First of all, make sure there's a nominal type that corresponds to the
       * expression being matched, and that we have its definition. *)
      let hint = Option.map (fun x -> x ^ "-match") hint in
      let env, x = check_expression env ?hint e in
      let nominal_type =
        try
          List.find (function
            | TyPoint p ->
                Log.check (is_type env p) "Invalid permission";
                has_definition env p
            | TyApp _ as t ->
                let cons, _args = flatten_tyapp t in
                let p = !!cons in
                Log.check (is_type env p) "Invalid permission";
                has_definition env p
            | _ ->
                false
          ) (get_permissions env x)
        with Not_found ->
          raise_error env (NotNominal x)
      in

      TypePrinter.(
        Log.debug ~level:3 "The matched expression has type %a"
          ptype (env, nominal_type)
      );

      let nominal_cons, nominal_args = flatten_tyapp nominal_type in
      let nominal_point = !!nominal_cons in

      (* Now, check that all the patterns are valid ones. Our matches only allow
       * to match on data types only. Use a let-binding to destructure a
       * tuple... *)
      let constructors = List.map (fun (pat, _) ->
        match pat with
        | PConstruct (datacon, _) ->
            let p =
              try
                type_for_datacon env datacon
              with Not_found ->
                raise_error env (MatchBadDatacon (nominal_type, datacon))
            in
            if not (same env p nominal_point) then
              raise_error env (MatchBadDatacon (nominal_type, datacon));
            datacon
        | _ ->
            raise_error env (MatchBadPattern pat)
      ) patexprs in

      (* Type-check each branch separately, returning an environment for that
       * branch as well as a point. *)
      let sub_envs = List.map2 (fun (pat, expr) datacon ->
        (* Refine the permissions. We *have* to remove the previous permission,
         * otherwise this is unsound, even with duplicable permissions. *)
        let env = replace_term env x (fun binding ->
          let permissions' = binding.permissions in
          (* Assert while we can *)
          let permissions = List.filter (fun x -> x != nominal_type) permissions' in
          Log.check (List.length permissions = List.length permissions' - 1)
            "We didn't strip the right number of permissions";
          { binding with permissions }
        ) in
        (* Trade the old permission for the new one. *)
        let branch =
          find_and_instantiate_branch env nominal_point datacon nominal_args
        in
        let env = Permissions.add env x (TyConcreteUnfolded branch) in
        let env, { subst_expr; _ } =
          check_bindings env Nonrecursive [pat, EPoint x]
        in
        let expr = subst_expr expr in
        let hint = Option.map (fun x -> x ^ "-" ^ (Datacon.print datacon)) hint in
        check_expression env ?hint expr
      ) patexprs constructors in

      (* Combine all of these left-to-right to obtain a single return
       * environment *)
      Hml_List.reduce (Merge.merge_envs env) sub_envs


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
        | PPoint p ->
            Some (Variable.print (get_name env p))
        | _ ->
            None
      in
      let env, point = check_expression env ?hint expr in
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
