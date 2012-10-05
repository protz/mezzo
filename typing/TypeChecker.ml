open Types
open TypeErrors
open Expressions
open Utils


(* -------------------------------------------------------------------------- *)

let add_hint =
  Permissions.add_hint
;;


(* The condition of an if-then-else statement is well-typed if it is a
 * data type with two branches. *)
let is_data_type_with_two_constructors env t =
  let has_two_branches p =
    if is_type env p then
      match get_definition env p with
      | Some (Some (_, branches), _) ->
          List.length branches = 2
      | _ ->
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
  let is_polymorphic = ref false in
  (* Instantiate all universally quantified variables with flexible variables. *)
  let rec flex = fun env -> function
    | TyForall ((binding, flavor), t) ->
        is_polymorphic := !is_polymorphic || flavor = CanInstantiate;
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
          TypePrinter.pvar fname;
        flex_deconstruct t
  in
  (* Warn the user if relying on our inference of polymorphic function calls. *)
  if !is_polymorphic then begin
    let error = TypeErrors.PolymorphicFunctionCall in
    if !Options.pedantic then
      TypeErrors.raise_error env error
    else
      Log.warn "%a" TypeErrors.print_error (env, error);
  end;
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


let check_return_type (env: env) (point: point) (t: typ): unit =
  TypePrinter.(
    let _, binder = find_term env point in
    Log.debug ~level:4 "Expecting return type %a; permissions for the point: %a"
      ptype (env, t)
      pdoc (print_permission_list, (env, binder));
    (* TestUtils.print_env env ;*)
  );
    
  match Permissions.sub env point t with
  | Some _ ->
      ()
  | None ->
      let open TypePrinter in
      Log.debug ~level:4 "%a\n------------\n" penv env;
      raise_error env (ExpectedType (t, point))
;;


let type_for_function_def (expression: expression): typ =
  match expression with
  | EFun (bindings, arg, return_type, _) ->
      let t = TyArrow (arg, return_type) in
      fold_forall bindings t
  | _ ->
      Log.error "[type_for_function_def], as the name implies, expects a \
        function expression...";
;;



(** [unify_pattern] is useful when type-checking [let pat = e] where [pat] is
 * a pattern and [e] is an expression. Type-checking [e] will add a new
 * permission to a point named [p]. We then need to glue the points in the
 * pattern to the intermediate points in the permission for [p]. If, for
 * instance, [pat] is [(p1, p2)] and [p @ (=p'1, =p'2)] holds, this function
 * will merge [p1] and [p'1], as well as [p2] and [p'2]. *)
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


(** [merge_type_annotations] is useful when the context provides a type
 * annotation and we hit a [EConstraint] expression. We need to make sure the
 * type annotations are consistent: (unknown, τ) and (σ, unknown) are consistent
 * type annotations; τ and τ are. We are conservative, and refuse to merge a lot
 * other cases: (τ | σ) and (τ | σ') should probably be merged in a clever
 * manner, but that's too complicated. *)
let merge_type_annotations env t1 t2 =
  let error () =
    raise_error env (ConflictingTypeAnnotations (t1, t2))
  in
  let rec merge_type_annotations t1 t2 =
    match t1, t2 with
    | _, _ when t1 = t2 ->
        t1
    | TyUnknown, _ ->
        t2
    | _, TyUnknown ->
        t1
    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        TyTuple (List.map2 merge_type_annotations ts1 ts2)
    | TyConcreteUnfolded (datacon1, fields1),
      TyConcreteUnfolded (datacon2, fields2)
      when Datacon.equal datacon1 datacon2 && List.length fields1 = List.length fields2 ->
        TyConcreteUnfolded (datacon1, List.map2 (fun f1 f2 ->
          match f1, f2 with
          | FieldValue (f1, t1), FieldValue (f2, t2) when Field.equal f1 f2 ->
              FieldValue (f1, merge_type_annotations t1 t2)
          | _ ->
              error ()
        ) fields1 fields2)
    | _ ->
        error ()
  in
  merge_type_annotations t1 t2
;;



let rec check_expression (env: env) ?(hint: name option) ?(annot: typ option) (expr: expression): env * point =

  (* TEMPORARY this is just a quick and dirty way to talk about user-defined
   * types. This is lazy because we want to write simple test cases that do not
   * define the "int" type. *)
  let make_lazy_getter t = lazy begin
    try
      find_type_by_name env t
    with Not_found ->
      Log.error "please define type %s" t
  end in
  let int = make_lazy_getter "int" in

  (* [return t] creates a new point with type [t] available for it, and returns
   * the environment as well as the point *)
  let return env t =
    (* Not the most clever function, but will do for now on *)
    let hint = Option.map_none (Auto (Variable.register (fresh_name "/x_"))) hint in
    let env, x = bind_term env hint env.location false in
    let env = Permissions.add env x t in
    env, x
  in

  match expr with
  | EConstraint (e, t) ->
      let annot = match annot with
        | Some t' -> merge_type_annotations env t t'
        | None -> t
      in
      let env, p = check_expression env ?hint ~annot e in
      check_return_type env p t;
      env, p

  | EVar _ ->
      Log.error "[check_expression] expects an expression where all variables \
        has been opened";

  | EPoint p ->
      env, p

  | ELet (rec_flag, patexprs, body) ->
      let env, { subst_expr; _ } = check_bindings env rec_flag patexprs in
      let body = subst_expr body in
      check_expression env ?annot body


  | EFun (vars, arg, return_type, body) ->
      List.iter (fun binding ->
        let open TypePrinter in
        let open ExprPrinter in
        Log.debug "%a" pdoc (print_binder, binding)
      ) vars;
      (* TODO we should have a separate pass that performs optimizations on a
       * [Expressions.expression] tree with a [Types.env] environment. Right
       * now, there's no such thing, so I'm putting this optimization here as
       * a temporary measure.
       *
       * Actually it would be hard to un-entangle the two phases, because
       * [check_bindings] needs to put in the environment the simplified version
       * of the type for recursive functions... *)
      let vars, arg, return_type, body =
        TypeOps.simplify_function_def env vars arg return_type body
      in
      let expr = EFun (vars, arg, return_type, body) in
      Log.debug ~level:4 "Type-checking function body, desugared type %a \
        desugared body %a"
        TypePrinter.ptype (env, type_for_function_def expr) 
        ExprPrinter.pexpr (env, body);

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
      let vars = List.map fst vars in
      let sub_env, { subst_type; subst_expr; _ } = bind_vars sub_env vars in
      let arg = subst_type arg in
      let return_type = subst_type return_type in
      let body = subst_expr body in

      (* Collect all the permissions that the arguments bring into scope, add
       * them into the environment for checking the function body. *)
      let _, perms = Permissions.collect arg in
      let _, constraints = Permissions.collect_constraints arg in
      let sub_env = Permissions.add_constraints sub_env constraints in
      let sub_env = List.fold_left Permissions.add_perm sub_env perms in

      (* Type-check the function body. *)
      let sub_env, p = check_expression sub_env ~annot:return_type body in

      begin match Permissions.sub sub_env p return_type with
      | Some _ ->
          (* Return the entire arrow type. *)
          let expected_type = type_for_function_def expr in
          return env expected_type
      | None ->
          raise_error sub_env (NoSuchPermission return_type)
      end

  | EAssign (e1, fname, e2) ->
      let hint = add_hint hint (Field.print fname) in
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
                  | FieldPermission _ ->
                      Log.error "These should've been inserted in the environment"
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

  | EAssignTag (e1, datacon) ->
      (* Type-check [e1]. *)
      let env, p1 = check_expression env e1 in

      (* Find the type [datacon] corresponds to. *)
      let _, branches = def_for_datacon env datacon in
      let _, fields =
        List.find (fun (datacon', _) -> Datacon.equal datacon datacon') branches
      in
      let field_names = List.map (function
        | FieldValue (name, _) ->
            name
        | FieldPermission _ ->
            (* We should just subtract the requireed permissions from the
             * environment. *)
            Log.error "Not implemented yet"
      ) fields in

      let permissions = get_permissions env p1 in
      let found = ref false in
      let permissions = List.map (function
        | TyConcreteUnfolded (datacon', fieldexprs) as t ->
            (* The current type should be mutable. *)
            let flag, _ = def_for_datacon env datacon' in
            if flag <> SurfaceSyntax.Exclusive then
              raise_error env (AssignNotExclusive (t, datacon'));

            (* Also, the number of fields should be the same. *)
            if List.length fieldexprs <> List.length field_names then
              raise_error env (FieldCountMismatch (t, datacon));

            (* Change the field names. *)
            let fieldexprs = List.map2 (fun field -> function
              | FieldValue (_, e) ->
                  FieldValue (field, e)
              | FieldPermission _ ->
                  Log.error "These should've been inserted in the environment"
            ) field_names fieldexprs in

            if !found then
              Log.error "Two suitable permissions, strange...";
            found := true;

            (* And don't forget to change the datacon as well. *)
            TyConcreteUnfolded (datacon, fieldexprs)

        | _ as t ->
            t
      ) permissions in

      if not !found then
        raise_error env (CantAssignTag p1);

      let env = replace_term env p1 (fun binder -> { binder with permissions }) in
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
      let hint = add_hint hint (Field.print fname) in
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
      begin match eunloc e1 with
      | EApply _ ->
          raise_error env NoMultipleArguments
      | _ ->
          ()
      end;
      let hint1 = add_hint hint "fun" in
      let hint2 = add_hint hint "arg" in
      let env, x1 = check_expression env ?hint:hint1 e1 in
      let env, x2 = check_expression env ?hint:hint2 e2 in
      (* Give an error message that mentions the entire function call. We should
       * probably have a function called nearest_loc that returns the location
       * of [e2] so that we can be even more precise in the error message. *)
      let env, return_type = check_function_call env x1 x2 in
      return env return_type

  | ETApply (e, t, k) ->
      let env, x = check_expression env e in
      replace_term env x (fun binding ->
        let perms = binding.permissions in
        let found = ref false in
        let perms = List.map (function
          | TyForall (((_, k', _), CanInstantiate), t') ->
              if k <> k' then begin
                raise_error env (IllKindedTypeApplication (t, k, k'))
              end else begin
                found := true;
                tsubst t 0 t'
              end
          | _ as t ->
              t
        ) perms in
        if not !found then
          raise_error env (BadTypeApplication x);
        { binding with permissions = perms }
      ), x

  | ETuple exprs ->
      (* Propagate type annotations inside the tuple. *)
      let annotations = match annot with
        | Some (TyTuple annotations) when List.length annotations = List.length exprs ->
            List.map (fun x -> Some x) annotations
        | _ ->
            Hml_List.make (List.length exprs) (fun _ -> None)
      in
      let env, components = Hml_List.fold_left2i
        (fun i (env, components) expr annot ->
          let hint = add_hint hint (string_of_int i) in
          let env, p = check_expression env ?hint ?annot expr in
          env, (ty_equals p) :: components)
        (env, []) exprs annotations
      in
      let components = List.rev components in
      return env (TyTuple components)

  | EConstruct (datacon, fieldexprs) ->
      let annot = Option.map (expand_if_one_branch env) annot in
      (* Propagate type annotations inside the constructor. *)
      let annotations = match annot with
        | Some (TyConcreteUnfolded (_, fields)) ->
            let annots = List.map (function
                | FieldValue (name, t) ->
                    name, t
                | _ ->
                    assert false
              ) fields
            in
            (* Every field in the type annotation corresponds to a field in the
             * expression, i.e. the type annotation makes sense. *)
            if List.for_all (fun (name, _) ->
                List.exists (function
                  | name', _ ->
                      Field.equal name name'
                ) fieldexprs
            ) annots then
              annots
            else
              []
        | _ ->
            []
      in
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
      (* Find the annotation for one of the fields. *)
      let annot name =
        Hml_List.find_opt (function
          | name', t when Field.equal name name' ->
              Some t
          | _ ->
              None
        ) annotations
      in
      (* Do the bulk of the work. *)
      let env, remaining, fieldvals = List.fold_left (fun (env, remaining, fieldvals) -> function
        | FieldValue (name, _t) ->
            (* Actually we don't care about the expected type for the field. We
             * just want to make sure all fields are provided. *)
            let e, remaining = take env name remaining in
            let hint = add_hint hint (Field.print name) in
            let env, p = check_expression env ?hint ?annot:(annot name) e in
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

  | ELocated (e, p1, p2) ->
      let pos = env.location in
      let env = locate env (p1, p2) in
      let env, p = check_expression env ?hint ?annot e in
      locate env pos, p

  | EIfThenElse (explain, e1, e2, e3) ->
      let hint_1 = add_hint hint "if" in
      let env, x1 = check_expression env ?hint:hint_1 e1 in

      let env, (left_t, right_t) =
        match Hml_List.take_bool (is_data_type_with_two_constructors env) (get_permissions env x1) with
        | Some (permissions, t) ->
            let env = replace_term env x1 (fun binding -> { binding with permissions }) in
            let split_apply cons args =
              match get_definition env cons with
              | Some (Some (_, [b1; b2]), _) ->
                  let t1 = TyConcreteUnfolded (instantiate_branch b1 args) in
                  let t2 = TyConcreteUnfolded (instantiate_branch b2 args) in
                  t1, t2
              | _ ->
                  assert false
            in
            env, begin match t with
            | TyPoint p ->
                split_apply p []
            | TyApp _ ->
                let cons, args = flatten_tyapp t in
                split_apply !!cons args
            | TyConcreteUnfolded _ ->
                t, t
            | _ ->
                Log.error "Contradicts [is_data_type_with_two_constructors]";
            end
        | None ->
            raise_error env (NoTwoConstructors x1);
      in
      let left_env = Permissions.add env x1 left_t in
      let right_env = Permissions.add env x1 right_t in

      (* The control-flow diverges. *)
      let hint_l = add_hint hint "then" in
      let left = check_expression left_env ?hint:hint_l ?annot e2 in
      let hint_r = add_hint hint "else" in
      let right = check_expression right_env ?hint:hint_r ?annot e3 in

      let dest = Merge.merge_envs env ?annot left right in

      if explain then
        Debug.explain_merge dest [left; right];

      dest

  | EMatch (explain, e, patexprs) ->
      (* First of all, make sure there's a nominal type that corresponds to the
       * expression being matched, and that we have its definition. *)
      let hint = add_hint hint "match" in 
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
        let hint = add_hint hint (Datacon.print datacon) in

        check_expression env ?hint ?annot expr
      ) patexprs constructors in

      (* Combine all of these left-to-right to obtain a single return
       * environment *)
      let dest = Hml_List.reduce (Merge.merge_envs env ?annot) sub_envs in

      if explain then
        Debug.explain_merge dest sub_envs;

      dest

  | EGive (_, _)
  | ETake (_, _) ->
     assert false 

  | EExplained e ->
      let env, x = check_expression env ?hint e in
      Debug.explain env ~x;
      env, x

  | EFail ->
      let name = Auto (Variable.register "/inconsistent") in
      let env, x = bind_term env name env.location false in
      { env with inconsistent = true }, x



and check_bindings
  (env: env)
  (rec_flag: rec_flag)
  (patexprs: (pattern * expression) list): env * substitution_kit
  =
    let env, patexprs, subst_kit = bind_patexprs env rec_flag patexprs in
    let { subst_expr; subst_pat; _ } = subst_kit in
    let patterns, expressions = List.split patexprs in
    let expressions = List.map subst_expr expressions in
    let patterns = subst_pat patterns in
    let env = match rec_flag with
      | Recursive ->
          List.fold_left2 (fun env expr pat ->
            let expr = eunloc expr in
            match pat, expr with
            | PPoint p, EFun (vars, arg, return_type, body) ->
                (* We need to add the simplified type here. *)
                let vars, arg, return_type, body =
                  TypeOps.simplify_function_def env vars arg return_type body
                in
                let expr = EFun (vars, arg, return_type, body) in
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
            Some (get_name env p)
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
