(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

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
      | Some (Some (_, branches, _), _) ->
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
  | TyApp (cons, _) ->
      (* e.g. list a *)
      has_two_branches !!cons
  | TyConcreteUnfolded (datacon, _, _) ->
      (* e.g. False *)
      let _, branches, _ = def_for_datacon env datacon in
      List.length branches = 2
  | _ ->
      false
;;

let has_adopts_clause env t =
  match t with
  | TyPoint p ->
      get_adopts_clause env p
  | TyApp (cons, args) ->
      begin match get_adopts_clause env !!cons with
      | Some clause ->
          Some (instantiate_adopts_clause (Some clause) args)
      | None ->
          None
      end
  | TyConcreteUnfolded (_, _, clause) ->
      if FactInference.is_exclusive env t then
        Some clause
      else
        None
  | _ ->
      None
;;


(* Since everything is, or will be, in A-normal form, type-checking a function
 * call amounts to type-checking a point applied to another point. The default
 * behavior is: do not return a type that contains flexible variables. *)
let check_function_call (env: env) (f: point) (x: point): env * typ =
  Log.debug ~level:5 "[check_function_call], f = %a, x = %a, env below\n\n%a\n"
    TypePrinter.pnames (env, get_names env f)
    TypePrinter.pnames (env, get_names env x)
    TypePrinter.penv env;

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
          TypePrinter.pvar (env, fname);
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
  Log.debug ~level:5 "[check_function_call] %a - %a"
    TypePrinter.pnames (env, get_names env x)
    TypePrinter.ptype (env, t1);
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

  | PAs (p1, p2) ->
      let p2 = match p2 with
        | PPoint p2 ->
            p2
        | _ ->
            Log.error "Bad desugaring?!!"
      in
      let env = merge_left env point p2 in
      unify_pattern env p1 point

  | PTuple patterns ->
      let permissions = get_permissions env point in
      let t = Hml_List.map_some (function TyTuple x -> Some x | _ -> None) permissions in
      if List.length t = 0 then
        raise_error env (BadPattern (pattern, point));
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
          | TyConcreteUnfolded (datacon', x, _) when Datacon.equal datacon datacon' ->
              Some x
          | _ ->
              None)
        permissions
      in
      if List.length field_defs = 0 then
        raise_error env (BadPattern (pattern, point));
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

  | PAny ->
      env

;;


let refine_perms_in_place_for_pattern env point pat =
  let rec refine env point pat =
    match pat with
    | PAs (pat, _) ->
        refine env point pat

    | PTuple pats ->
        let points =
          match Hml_List.find_opt (function
            | TyTuple ts ->
                Some (List.map (function
                  | TySingleton (TyPoint p) ->
                      p
                  | _ ->
                      Log.error "expanded form"
                ) ts)
            | _ ->
                None
          ) (get_permissions env point) with
          | Some points ->
              points
          | None ->
              raise_error env (MatchBadTuple point)
        in
        List.fold_left2 refine env points pats

    | PConstruct (datacon, patfields) ->
        (* An easy way out. *)
        let fail () = raise_error env (MatchBadDatacon (point, datacon)) in
        let fail_if b = if b then fail () in

        (* Turn the return value of [find_and_instantiate_branch] into a type. *)
        let mkconcrete (dc, fields, clause) =
          TyConcreteUnfolded (dc, fields, clause)
        in

        (* Recursively refine the fields of a concrete type according to the
         * sub-patterns. *)
        let refine_fields env fields = List.fold_left (fun env (n2, pat2) ->
          let open ExprPrinter in
          let open TypePrinter in
          Log.debug "Field = %a, pat = %a" Field.p n2 ppat (env, pat2);
          List.iter (function
            | FieldValue (n1, t1) ->
                Log.debug "Field = %a, t = %a" Field.p n1 ptype (env, t1)
            | _ ->
                assert false
          ) fields;
          let point1 = match Hml_List.find_opt (function
            | FieldValue (n1, TySingleton (TyPoint p1)) when Field.equal n1 n2 ->
                Some p1
            | _ ->
                None
          ) fields with
          | Some p1 ->
              p1
          | None ->
              raise_error env (BadField (datacon, n2))
          in
          refine env point1 pat2
        ) env patfields in

        (* Find a permission that can be refined in there. *)
        begin match Hml_List.take (function
          | TyPoint p ->
              fail_if (not (has_definition env p));
              begin try
                let branch = find_and_instantiate_branch env p datacon [] in
                Some (env, mkconcrete branch)
              with Not_found ->
                (* Urgh [find_and_instantiate_branch] should probably throw
                 * something better... *)
                fail ()
              end
          | TyApp (cons, args) ->
              begin try
                let branch = find_and_instantiate_branch env !!cons datacon args in
                Some (env, mkconcrete branch)
              with Not_found ->
                fail ()
              end
          | TyConcreteUnfolded (datacon', fields', _) as t ->
              let is_ok =
                Datacon.equal datacon datacon' &&
                List.for_all (function
                  | FieldValue (n1, _), (n2, _) ->
                      Field.equal n1 n2
                  | _ ->
                      Log.error "not in order or not expanded"
                ) (List.combine fields' patfields)
              in
              fail_if (not is_ok);
              Some (env, t)
          | _ ->
              None
        ) (get_permissions env point) with
        | Some (remaining, (_, (env, t))) ->
            (* Now strip the permission we consumed... *)
            let env =
              replace_term env point (fun binding -> { binding with permissions = remaining})
            in
            (* Add instead its refined version -- this also makes sure it's in expanded form. *)
            let env = Permissions.add env point t in
            (* Find the resulting structural permission. *)
            let fields = Option.extract (Hml_List.find_opt (function
              | TyConcreteUnfolded (_, fields, _) ->
                  Some fields
              | _ ->
                  None
            ) (get_permissions env point)) in
            (* And recursively refine its fields now that they are in the
             * expanded form. *)
            refine_fields env fields
        | None ->
            fail ()
        end

    | _ ->
        env
  in
  refine env point pat
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
    | TyConcreteUnfolded (datacon1, fields1, clause1),
      TyConcreteUnfolded (datacon2, fields2, clause2)
      when Datacon.equal datacon1 datacon2 && List.length fields1 = List.length fields2 ->
        TyConcreteUnfolded (datacon1, List.map2 (fun f1 f2 ->
          match f1, f2 with
          | FieldValue (f1, t1), FieldValue (f2, t2) when Field.equal f1 f2 ->
              FieldValue (f1, merge_type_annotations t1 t2)
          | _ ->
              error ()
        ) fields1 fields2,
        merge_type_annotations clause1 clause2)
    | _ ->
        error ()
  in
  merge_type_annotations t1 t2
;;



let rec check_expression (env: env) ?(hint: name option) ?(annot: typ option) (expr: expression): env * point =

  (* TEMPORARY pas de risque que l'utilisateur masque ces définitions? *)
  let t_int = find_type_by_name env ~mname:"core" "int"
  and t_bool = find_type_by_name env ~mname:"core" "bool" in

  (* [return t] creates a new point with type [t] available for it, and returns
   * the environment as well as the point *)
  let return env t =
    (* Not the most clever function, but will do for now on *)
    let hint = Option.map_none (Auto (Variable.register (fresh_name "/x_"))) hint in
    let env, x = bind_term env hint env.location false in
    let env = Permissions.add env x t in
    match annot with
    | None ->
        env, x
    | Some t ->
        match Permissions.sub env x t with
        | Some _ ->
            env, x
        | None ->
            raise_error env (ExpectedType (t, x))
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
      (* TODO we should have a separate pass that performs optimizations on a
       * [Expressions.expression] tree with a [Types.env] environment. Right
       * now, there's no such thing, so I'm putting this optimization here as
       * a temporary measure.
       *
       * Actually it would be hard to un-entangle the two phases, because
       * [check_bindings] needs to put in the environment the simplified version
       * of the type for recursive functions... *)
      let vars, arg, return_type, body =
        TypeOps.prepare_function_def env vars arg return_type body
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
      let sub_env, { subst_type; subst_expr; _ } = bind_evars sub_env vars in
      let arg = subst_type arg in
      let return_type = subst_type return_type in
      let body = subst_expr body in

      (* Collect all the permissions that the arguments bring into scope, add
       * them into the environment for checking the function body. *)
      let t_noconstraints, constraints = Permissions.collect_constraints arg in
      let _, perms = Permissions.collect t_noconstraints in
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
      let hint = add_hint hint (Field.print fname.field_name) in
      let env, p1 = check_expression env ?hint e1 in
      let env, p2 = check_expression env e2 in
      let env = replace_term env p1 (fun binder ->
        let permissions = binder.permissions in
        let found = ref false in
        let permissions = List.map (fun t ->
            match t with
            | TyConcreteUnfolded (datacon, fieldexprs, clause) ->
                (* Check that datacon points to a type that is defined as
                 * exclusive. *)
                let flag, _, _ = def_for_datacon env datacon in
                if flag <> SurfaceSyntax.Exclusive then
                  raise_error env (AssignNotExclusive (t, datacon));

                (* Perform the assignment. *)
                let fieldexprs = List.map (function
                  | FieldValue (field, expr) ->
                      let expr = 
                        if Field.equal field fname.field_name then
                          begin match expr with
                          | TySingleton (TyPoint _) ->
                              if !found then
                                Log.error "Two matching permissions? That's strange...";
                              found := true;
                              fname.field_datacon <- datacon;
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
                TyConcreteUnfolded (datacon, fieldexprs, clause)
            | _ ->
                t
          ) permissions
        in
        if not !found then
          raise_error env (NoSuchField (p1, fname.field_name));
        { binder with permissions })
      in
      return env ty_unit

  | EAssignTag (e1, datacon) ->
      (* Type-check [e1]. *)
      let env, p1 = check_expression env e1 in

      (* Find the type [datacon] corresponds to. *)
      let _, branches, _ = def_for_datacon env datacon.datacon_name in
      let _, fields =
        List.find (fun (datacon', _) -> Datacon.equal datacon.datacon_name datacon') branches
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
        | TyConcreteUnfolded (datacon', fieldexprs, clause) as t ->
            (* The current type should be mutable. *)
            let flag, _, _ = def_for_datacon env datacon' in
            if flag <> SurfaceSyntax.Exclusive then
              raise_error env (AssignNotExclusive (t, datacon'));

            (* Also, the number of fields should be the same. *)
            if List.length fieldexprs <> List.length field_names then
              raise_error env (FieldCountMismatch (t, datacon.datacon_name));

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
            datacon.datacon_previous_name <- datacon';

            (* And don't forget to change the datacon as well. *)
            TyConcreteUnfolded (datacon.datacon_name, fieldexprs, clause)

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
      let hint = add_hint hint (Field.print fname.field_name) in
      let env, p = check_expression env ?hint e in
      let module M = struct exception Found of point end in
      begin try
        List.iter (fun t ->
          match t with
          | TyConcreteUnfolded (datacon, fieldexprs, _) ->
              List.iter (function
                | FieldValue (field, expr) ->
                    if Field.equal field fname.field_name then
                      begin match expr with
                      | TySingleton (TyPoint p) ->
                          fname.field_datacon <- datacon;
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
        raise_error env (NoSuchField (p, fname.field_name))
      with M.Found p' ->
        env, p'
      end

  | EApply (e1, e2) ->
      begin match eunloc e1 with
      | EApply _ ->
          if not (!Options.multiple_arguments) then
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
      let rec find_and_instantiate = function
        | TyForall (((name, k', loc), CanInstantiate), t') as t0 ->
            Log.debug "%a" TypePrinter.ptype (env, t0);
            let check_kind () =
              if k <> k' then
                raise_error env (IllKindedTypeApplication (t, k, k'))
            in
            begin match t with
            | Ordered t ->
                check_kind ();
                Some (tsubst t 0 t')
            | Named (x, t) ->
                let short_name =
                  match name with
                  | Auto _ ->
                      assert false
                  | User (_, x) ->
                      x
                in
                if Variable.equal x short_name then begin
                  check_kind ();
                  let t = tsubst t 0 t' in
                  let t = lift (-1) t in
                  Some t
                end else begin
                  match find_and_instantiate t' with
                  | Some t' ->
                      Some (TyForall (((name, k', loc), CanInstantiate), t'))
                  | None ->
                      None
                end
            end
        | _ ->
            None
      in
      (* Find something that works. *)
      let t = Hml_List.find_opt find_and_instantiate (get_permissions env x) in
      let t = match t with
        | Some t ->
            t
        | None ->
            raise_error env (BadTypeApplication x);
      in
      (* And return a fresh point with that new list of permissions. *)
      let name =
        match get_name env x with
        | User (_, x) ->
            Auto (Variable.register (Variable.print x ^ "_inst"))
        | _ as x ->
            x
      in
      let env, x = bind_term env name (get_location env x) false in
      Permissions.add env x t, x

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
      let clause = match annot with
        | Some (TyConcreteUnfolded (_, _, clause)) ->
            clause
        | _ ->
            ty_bottom
      in
      let annotations = match annot with
        | Some (TyConcreteUnfolded (_, fields, _)) ->
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
      let _flag, branches, _ = def_for_datacon env datacon in
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

      (* Evaluate the fields in the order they come in the source file. *)
      let env, fieldexprs = List.fold_left (fun (env, acc) (name, e) ->
        let hint = add_hint hint (Field.print name) in
        let env, p = check_expression env ?hint ?annot:(annot name) e in
        env, (name, p) :: acc
      ) (env, []) fieldexprs in

      (* Do the bulk of the work. *)
      let env, remaining, fieldvals = List.fold_left (fun (env, remaining, fieldvals) -> function
        | FieldValue (name, _t) ->
            (* Actually we don't care about the expected type for the field. We
             * just want to make sure all fields are provided. *)
            let p, remaining = take env name remaining in
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
      return env (TyConcreteUnfolded (datacon, fieldvals, clause))


  | EInt _ ->
      return env t_int

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
              | Some (Some (_, [b1; b2], clause), _) ->
                  let dc1, branch1 = instantiate_branch b1 args in
                  let dc2, branch2 = instantiate_branch b2 args in
                  let clause = instantiate_adopts_clause clause args in
                  let t1 = TyConcreteUnfolded (dc1, branch1, clause) in
                  let t2 = TyConcreteUnfolded (dc2, branch2, clause) in
                  t1, t2
              | _ ->
                  assert false
            in
            env, begin match t with
            | TyPoint p ->
                split_apply p []
            | TyApp (cons, args) ->
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
      let hint = add_hint hint "match" in 
      let env, x = check_expression env ?hint e in

      (* Type-check each branch separately, returning an environment for that
       * branch as well as a point. *)
      let sub_envs = List.map (fun (pat, expr) ->
        let env = refine_perms_in_place_for_pattern env x pat in
        let env, { subst_expr; _ } =
          check_bindings env Nonrecursive [pat, EPoint x]
        in
        let expr = subst_expr expr in
        check_expression env ?annot expr
      ) patexprs in

      (* Combine all of these left-to-right to obtain a single return
       * environment *)
      let dest = Hml_List.reduce (Merge.merge_envs env ?annot) sub_envs in

      if explain then
        Debug.explain_merge dest sub_envs;

      dest

  | EGive (x, e) ->
      (* Small helper function. *)
      let replace_clause perm clause =
        match perm with
        | TyConcreteUnfolded (dc, branch, _old_clause) ->
            TyConcreteUnfolded (dc, branch, clause)
        | _ ->
            Log.error "[perm] must be a nominal type, and we don't allow the \
              user to declare a nominal type that adopts [ty_bottom]."
      in
      (* Find the type annotation provided on x, if any. *)
      let env, x, t =
        match eunloc x with
        | EConstraint (_, t) ->
            (* Check the entire [EConstraint] thing, so that we can fail early
             * and with a good location if the user messed up their type
             * annotations. *)
            let env, x = check_expression env ?hint x in
            env, x, Some t
        | _ ->
            let env, x = check_expression env ?hint x in
            env, x, None
      in
      let env, y = check_expression env ?hint e in
      (* Find the adopts clause for this structural permission. *)
      begin match Hml_List.take (has_adopts_clause env) (get_permissions env y) with
      | None ->
          raise_error env (NoAdoptsClause y)
      | Some (remaining_perms, (perm, clause)) ->
          if equal env clause ty_bottom then
            (* The clause is unspecified; we must rely on the user-provided type
             * annotation to find out what it is. *)
            match t with
            | None ->
                raise_error env AdoptsNoAnnotation
            | Some t ->
                (* First of all, check that the user wants to adopt something
                 * legit. *)
                if not (FactInference.is_exclusive env t) then
                  raise_error env (BadFactForAdoptedType (y, t, FactInference.analyze_type env t));
                (* The clause is now [t]. Extract it from the list of available
                 * permissions for [x]. We know it works because we type-checked
                 * the whole [EConstraint] already. *)
                let env = Option.extract (Permissions.sub env x t) in
                (* Refresh the structural permission for [e], using the new
                 * clause. *)
                let perm = replace_clause perm t in
                let env = replace_term env y (fun raw -> { raw with permissions = perm :: remaining_perms }) in
                (* We're done. *)
                return env ty_unit
          else begin
            Log.check (FactInference.is_exclusive env clause)
              "We erroneously allowed a non-exclusive adopts clause";
            (* The clause is known. Just take the required permission out of the
             * permissions for x. *)
            match Permissions.sub env x clause with
            | Some env ->
                return env ty_unit
            | None ->
                raise_error env (NoSuitableTypeForAdopts (x, clause))
          end
      end

  | ETake (x, e) ->
      let env, x = check_expression env ?hint x in
      if not (List.exists (equal env TyDynamic) (get_permissions env x)) then
        raise_error env (NotDynamic x);
      let env, y = check_expression env ?hint e in
      begin match Hml_List.find_opt (has_adopts_clause env) (get_permissions env y) with
      | None ->
          raise_error env (NoAdoptsClause y)
      | Some clause ->
          let env = Permissions.add env x clause in
          return env ty_unit
      end

  | EOwns (y, x) ->
      (* Careful: the order of the parameters is reversed compared to [EGive]
	 and [ETake]. *)
      let env, x = check_expression env ?hint x in
      if not (List.exists (equal env TyDynamic) (get_permissions env x)) then
        raise_error env (NotDynamic x);
      let env, y = check_expression env ?hint y in
      (* Check that the type of [y] has an adopts clause (which implies that
	 it is exclusive). This is a stronger condition than strictly required
	 for type soundness (no condition on [y] would be enough) and for
	 stability (exclusive-ness would be enough), but it should allow us
	 to detect a few more programmer errors. *)
      (* TEMPORARY if we have an exclusive permission for [x], then we could
	 emit a warning, because in this case [y owns x] is certain to return
	 false. *)
      if not (List.exists (FactInference.is_exclusive env) (get_permissions env y)) then
        raise_error env (NoAdoptsClause y);
      return env t_bool

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
            | PPoint p, EFun _ ->
                let t = type_for_function_def expr in
                (* [add] takes care of simplifying the function type *)
                Permissions.add env p t
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

let check_declaration_group
    (env: env)
    (declarations: declaration_group)
    (toplevel_items: toplevel_item list): env * toplevel_item list =
  let rec check_declaration_group env declarations acc =
    match declarations with
    | DLocated (declarations, p1, p2) :: tl ->
        let env = locate env (p1, p2) in
        check_declaration_group env (declarations :: tl) acc
    | DMultiple (rec_flag, patexprs) :: tl ->
        let env, { subst_decl; points; _ } = check_bindings env rec_flag patexprs in
        let tl = subst_decl tl in
        check_declaration_group env tl (points :: acc)
    | [] ->
        env, acc
  in
  let env, acc = check_declaration_group env declarations [] in
  (* Alright, this is an UGLY manipulation of De Bruijn indices... *)
  let points = List.rev acc in
  let points = List.flatten points in
  (* List kept in reverse, the usual trick. *)
  let points = List.rev points in
  let subst_toplevel_items b =
    Hml_List.fold_lefti (fun i b point ->
      let b = tsubst_toplevel_items (TyPoint point) i b in
      esubst_toplevel_items (EPoint point) i b) b points
  in
  (* ...but it works! *)
  env, subst_toplevel_items toplevel_items
;;
