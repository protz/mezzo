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

open Kind
open Either
open TypeCore
open DeBruijn
open Types
open TypeErrors
open ExpressionsCore
open Expressions

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
      | Some (Concrete branches) ->
          List.length branches = 2
      | _ ->
          false
    else
      false
  in
  match expand_if_one_branch env t with
  | TyOpen p ->
      (* e.g. bool *)
      has_two_branches p
  | TyApp (cons, _) ->
      (* e.g. list a *)
      has_two_branches !!cons
  | TyConcrete branch ->
      (* e.g. False *)
      let branches = branches_for_branch env branch in
      List.length branches = 2
  | _ ->
      false
;;

(* Does [x @ t] allow [x] to adopt? If [t] is an algebraic data type,
   then an adopts clause of [TyBottom] means that [x] cannot
   adopt. However, if [t] is unfolded, then an adopts clause of
   [TyBottom] does allow [x] to adopt, by covariance of the adopts
   clause. *)
let has_adopts_clause env t =
  match t with
  | TyOpen p ->
      let clause = get_adopts_clause env p in
      is_non_bottom clause
  | TyApp (cons, args) ->
      let clause = get_adopts_clause env !!cons in
      let clause = instantiate_type clause args in
      is_non_bottom clause
  | TyConcrete branch ->
      if FactInference.is_exclusive env t then
        Some branch.branch_adopts
      else
        None
  | _ ->
      None
;;


(* This function expands type abbreviations / data types with one branch even
 * under a "x @ _" anchored permission. *)
let expand_if_one_branch_even_if_anchored env = function
  | TyAnchoredPermission (x, t) ->
      TyAnchoredPermission (x, expand_if_one_branch env t)
  | u ->
      expand_if_one_branch env u
;;

(* This is a third-order helper function that starts with environment [env].
 * - If no concrete type is available for [x], it calls [failure env].
 * - If at least one concrete type [TyConcrete b] is available for [x]...
 *
 * It calls [success b k].
 * The [success] function modifies the branch [b]. When [success] is done, it
 *  hands over control to [k], by calling [k b' k'], where [b'] is the new
 *  branch that replaces [b]. [success] is not supposed to modify any
 *  environment.
 * The [k] function updates the original environment with the new branch [b'],
 *  producing an updated environment [env']. It then calls [k' env'].
 * The [k'] function takes the modified environment and produces the final
 *  value.
 * *)
let transform_constructor_permission
  (env: env)
  (x: var)
  (success: branch -> (branch -> (env -> 'a) -> 'a) -> 'a)
  (failure: unit -> 'a) =
    let permissions = get_permissions env x in
    let concrete, not_concrete = List.partition is_concrete permissions in
    match concrete with
    | [] ->
        failure ()
    | hd :: tl ->
        if tl <> [] then
          Log.debug ~level:5 "Several concrete permissions. Weird, but maybe ok.";
        success (assert_concrete hd) (fun branch k ->
          let new_permissions =
            TyConcrete branch :: tl @ not_concrete
          in
          let env = set_permissions env x new_permissions in
          k env
        )
;;

let replace_field
  (branch: branch)
  (field: Field.name)
  (f: int -> var -> typ) =
    let branch_fields = List.mapi (fun i (field', t) ->
      if Field.equal field field' then
        field', f i !!=t
      else
        field', t
    ) branch.branch_fields in
    { branch with branch_fields }
;;

let check_function_call (env: env) ?(annot: typ option) (f: var) (x: var): env * typ =
  Log.debug ~level:5 "[check_function_call], f = %a, x = %a, env below\n\n%a\n"
    TypePrinter.pnames (env, get_names env f)
    TypePrinter.pnames (env, get_names env x)
    TypePrinter.penv env;

  (* Find a suitable permission for [f] first *)
  let rec is_quantified_arrow = function
    | TyQ (Forall, _, _, t) ->
        is_quantified_arrow t
    | TyArrow _ ->
        true
    | _ ->
        false
  in
  let permissions = List.filter is_quantified_arrow (get_permissions env f) in

  (* Instantiate all universally quantified variables with flexible variables. *)
  let rec flex = fun env -> function
    | TyQ (Forall, binding, _, t) ->
        let env, t, var = bind_flexible_in_type env binding t in
        let env, t, vars = flex env t in
        let vars =
          match binding with
          | User (_, name), _, _ -> (name, var) :: vars
          | Auto _, _, _ -> vars
        in
        env, t, vars
    | _ as t ->
        env, t, []
  in

  (* Deconstruct a possibly-quantified arrow. *)
  let flex_deconstruct_arrow env t =
    let env, t, vars = flex env t in
    match t with
    | TyArrow (t1, t2) ->
        env, (t1, t2), vars
    | _ ->
        assert false
  in

  (* Try to give some useful error messages in case we have found not enough or
   * too many suitable types for [f]. *)

  let valid, invalid = List.fold_right (fun t (valid, invalid) ->
    let env, (t1, t2), vars = flex_deconstruct_arrow env t in

    (* Try to instantiate flexibles in [t2] better by using the context-provided
     * type annotation. *)
    let env =
      match annot with
      | Some annot ->
          Log.debug ~level:5 "[sub-annot]";
          begin
            let sub_env = env in
            match Permissions.sub_type sub_env t2 annot |> Permissions.drop_derivation with
            | Some sub_env ->
                Log.debug ~level:5 "[sub-annot SUCCEEDED]";
                Permissions.import_flex_instanciations env sub_env
            | None ->
                env
          end
      | None ->
          env
    in

    (* Examine [x]. [sub] will take care of running collect on [t1] so that the
     * expected permissions are subtracted as well from the environment. *)
    Log.debug ~level:5 "[check_function_call] %a - %a"
      TypePrinter.pnames (env, get_names env x)
      TypePrinter.ptype (env, t1);

    match Permissions.sub env x t1 with
    | Left (env, derivation) ->
        (env, derivation, (t1, t2), vars) :: valid, invalid
    | Right derivation ->
        valid, (env, derivation, (t1, t2)) :: invalid
  ) permissions ([], []) in

  match valid, invalid with
  | [], [] ->
      raise_error env (NotAFunction f)
  | [], (env, d, (t1, _)) :: _ ->
      raise_error env (ExpectedType (t1, x, d))
  | (env', d, (_, t2), vars) :: xs, _ ->
      if xs <> [] then
        may_raise_error env (SeveralWorkingFunctionTypes f);
      List.iter (fun (name, var) ->
        may_raise_error env (Instantiated (name, TyOpen var))
      ) vars;

      Log.debug ~level:5 "[check_function_call] subtraction succeeded \\o/";
      Log.debug ~level:6 "\nDerivation: %a\n" DerivationPrinter.pderivation d;
      env', t2
;;


let check_return_type (env: env) (var: var) (t: typ): env * var =
  TypePrinter.(
    Log.debug ~level:4 "Expecting return type %a; permissions for the var: %a"
      ptype (env, t)
      MzPprint.pdoc (print_permission_list, (env, get_permissions env var));
    (* TestUtils.print_env env ;*)
  );
    
  match Permissions.sub env var t with
  | Left (env, _) ->
      Permissions.add env var t, var
  | Right derivation ->
      let open TypePrinter in
      Log.debug ~level:4 "%a\n------------\n" penv env;
      raise_error env (ExpectedType (t, var, derivation))
;;


let rec type_for_function_def = function
  | EBigLambdas (bindings, e) ->
      fold_forall bindings (type_for_function_def e)
  | ELambda (arg, return_type, _) ->
      TyArrow (arg, return_type)
  | _ ->
      Log.error "[type_for_function_def], as the name implies, expects a \
        function expression...";
;;



(** [unify_pattern] is useful when type-checking [let pat = e] where [pat] is
 * a pattern and [e] is an expression. Type-checking [e] will add a new
 * permission to a var named [p]. We then need to glue the vars in the
 * pattern to the intermediate vars in the permission for [p]. If, for
 * instance, [pat] is [(p1, p2)] and [p @ (=p'1, =p'2)] holds, this function
 * will merge [p1] and [p'1], as well as [p2] and [p'2].
 *)
let rec unify_pattern (env: env) (pattern: pattern) (var: var): env =

  match pattern with
  | PVar _ ->
      Log.error "[unify_pattern] takes a pattern that has been run through \
        [subst_pat] first"

  | POpen p ->
      (* [var] is the descriptor that has all the information; [p] just has
       * [=p] as a permission, and maybe an extra one if it's a [val rec f]
       * where [f] is a recursive function *)
      Option.extract (merge_left env var p)

  | PAs (p1, p2) ->
      let p2 = match p2 with
        | POpen p2 ->
            p2
        | _ ->
            Log.error "Bad desugaring?!!"
      in
      let env = Option.extract (merge_left env var p2) in
      unify_pattern env p1 var

  | PTuple patterns ->
      let permissions = get_permissions env var in
      let t = MzList.map_some (function TyTuple x -> Some x | _ -> None) permissions in
      if List.length t = 0 then
        raise_error env (BadPattern (pattern, var));
      let t = List.hd t in
      if List.length t <> List.length patterns then
        raise_error env (BadPattern (pattern, var));
      List.fold_left2 (fun env pattern component ->
        unify_pattern env pattern !!=component
      ) env patterns t

  | PConstruct (datacon, field_pats) ->
      let permissions = get_permissions env var in
      let field_defs = MzList.map_some
        (function
          | TyConcrete branch when resolved_datacons_equal env datacon branch.branch_datacon ->
              Some branch.branch_fields
          | _ ->
              None)
        permissions
      in
      if List.length field_defs = 0 then
        raise_error env (BadPattern (pattern, var));
      let field_defs = List.hd field_defs in
      List.fold_left (fun env (name, pat) ->
        (* The pattern fields may not all be there or in an arbitrary order. *)
        let _, t =
          try
            List.find (fun (name', _) -> Field.equal name name') field_defs
          with Not_found ->
            raise_error env (NoSuchFieldInPattern (pattern, name))
        in
        unify_pattern env pat !!=t
      ) env field_pats

  | PAny ->
      env

;;


(** This function takes a permission (e.g. "list int") and refines it following
 * a given pattern (e.g. "Cons { head; _ }") thus changing it into something
 * more precise (e.g. "Cons { head = h; tail = t } * h @ ... * t @ ..."). The
 * variables in the pattern are not tied to the structure points: this is the
 * job of [unify_pattern], which will be typically called by [check_bindings].
 * *)
let refine_perms_in_place_for_pattern env var pat =
  (* TEMPORARY MatchBadTuple and MatchBadDatacon should not produce a type
     error; they should produce an inconsistent environment (hence cause
     the whole branch to be skipped) if the intersection is empty *)
  let rec refine env var pat =
    match pat with
    | PAs (pat, _) ->
        refine env var pat

    | PTuple pats ->
        (** This is an easy case: there's nothing to refine here (a tuple type
         * can always match a tuple type), so recursively refine the tuple
         * components. *)
        let vars =
          match MzList.find_opt (function
            | TyTuple ts ->
                Some (List.map (!!=) ts)
            | _ ->
                None
          ) (get_permissions env var) with
          | Some vars ->
              vars
          | None ->
              raise_error env (MatchBadTuple var)
        in
        (* We need to check here that the lengths match because of the call to
         * [fold_left2]. This is duplicating the check that [unify_pattern]
         * performs. However, since [unify_pattern] is not always preceded by a
         * call to [refine_perms_in_place_for_pattern], we have to check in both
         * places. *)
        if List.length vars <> List.length pats then
          raise_error env (MatchBadTuple var);
        List.fold_left2 refine env vars pats

    | PConstruct (datacon, patfields) ->
        (* An easy way out. *)
        let fail () = raise_error env (MatchBadDatacon (var, snd datacon)) in
        let fail_if b = if b then fail () in

        (* Recursively refine the fields of a concrete type according to the
         * sub-patterns. This will be called once we have found the types of the
         * corresponding [fields]. *)
        let refine_fields env fields = List.fold_left (fun env (n2, pat2) ->
          match MzList.find_opt (fun (n1, t1) ->
            if Field.equal n1 n2 then
              Some !!=t1
            else
              None
          ) fields with
          | Some p1 ->
              refine env p1 pat2
          | None ->
              raise_error env (BadField (snd datacon, n2))
        ) env patfields in

        (* Find a permission that can be refined in there. *)
        begin match MzList.take (function
          | TyOpen p ->
              let p', datacon = datacon in
              fail_if (not (same env p !!p'));
              fail_if (get_definition env p = None);
              begin try
                let branch = find_and_instantiate_branch env p datacon [] in
                Some (env, branch)
              with Not_found ->
                (* Urgh [find_and_instantiate_branch] should probably throw
                 * something better... *)
                fail ()
              end
          | TyApp (cons, args) ->
              let p', datacon = datacon in
              fail_if (not (same env !!cons !!p'));
              begin try
                let branch = find_and_instantiate_branch env !!cons datacon args in
                Some (env, branch)
              with Not_found ->
                fail ()
              end
          | TyConcrete branch' as t ->
              if not (resolved_datacons_equal env datacon branch'.branch_datacon) then
                (* [refine_fields] takes care of checking that the fields in the
                 * pattern all map to an existing field name for the structural
                 * permission we found. We could technically skip this check
                 * since [unify_pattern] will check that again for us, but well,
                 * better do it now. *)
                fail ();
              Some (env, t)
          | _ ->
              None
        ) (get_permissions env var) with
        | Some (remaining, (_, (env, t))) ->
            (* Now strip the permission we consumed... *)
            let env =
              set_permissions env var remaining
            in
            (* Add instead its refined version -- this also makes sure it's in expanded form. *)
            let env = Permissions.add env var t in
            (* Find the resulting structural permission. *)
            let fields = Option.extract (MzList.find_opt (function
              | TyConcrete branch ->
                  Some branch.branch_fields
              | _ ->
                  None
            ) (get_permissions env var)) in
            (* And recursively refine its fields now that they are in the
             * expanded form. *)
            refine_fields env fields
        | None ->
            fail ()
        end

    | _ ->
        env
  in
  refine env var pat
;;

let rec check_expression (env: env) ?(hint: name option) ?(annot: typ option) (expr: expression): env * var =

  let find_qualified_type m x =
    (* lazy because we need to typecheck the core modules too! *)
    lazy begin
      let x = Exports.find_qualified_var env (Module.register m) (Variable.register x) in
      TyOpen x
    end
  in
  let t_int = find_qualified_type "int" "int" in
  let t_bool = find_qualified_type "bool" "bool" in

  (* [return t] creates a new var with type [t] available for it, and returns
   * the environment as well as the var *)
  let return env t =
    (* Not the most clever function, but will do for now on *)
    let hint = Option.map_none (fresh_auto_name "/x_") hint in
    let env, x = bind_rigid env (hint, KTerm, location env) in
    let env = Permissions.add env x t in
    match annot with
    | None ->
        env, x
    | Some t ->
        (* jp: This is possibly quadratic, so I tried removing that check to see
         * whether it helped. Turns out it does not change performances the
         * least bit, so I'm leaving it in the hope that it gives potentially
         * better error messages. *)
        match Permissions.sub env x t with
        | Left _ ->
            env, x
        | Right d ->
            raise_error env (ExpectedType (t, x, d))
  in

  match expr with
  | EConstraint (e, t) ->
      (* We used to be smart and merge type annotations but not a single test
       * file used this (dubious) feature, so it was removed. *)
      let annot = match annot with
        | Some t' -> raise_error env (ConflictingTypeAnnotations (t, t'))
        | None -> t
      in
      let env, p = check_expression env ?hint ~annot e in
      check_return_type env p t

  | EAssert p ->
      begin match Permissions.sub_perm env p with
      | Left (env, _) ->
          let env = Permissions.add_perm env p in
          return env ty_unit
      | Right derivation ->
          raise_error env (ExpectedPermission (p, derivation))
      end

  | EPack (u, t') ->
      (* Type-checking « pack u witness t' » with « u = ∃α.t » amounts to:
       * - subtract [t'/α]t
       * - add u
       * *)
      let t =
        match expand_if_one_branch_even_if_anchored env u with
        | TyQ (Exists, _, UserIntroduced, t) ->
            tsubst t' 0 t
        | TyAnchoredPermission (x, TyQ (Exists, _, UserIntroduced, t)) ->
            TyAnchoredPermission (x, tsubst t' 0 t)
        | _ ->
            raise_error env PackWithExists
      in
      begin match Permissions.sub_perm env t with
      | Left (env, _) ->
          let env = Permissions.add_perm env u in
          return env ty_unit
      | Right derivation ->
          raise_error env (ExpectedPermission (u, derivation))
      end


  | EVar _ ->
      Log.error "[check_expression] expects an expression where all variables \
        has been opened";

  | EOpen p ->
      env, p

  | ELet (rec_flag, patexprs, body) ->
      let env, { subst_expr; _ } = check_bindings env rec_flag patexprs in
      let body = subst_expr body in
      check_expression env ?annot body

  | ELetFlex (binding, e) ->
      (* Bind (manually) the variable as flexible. *)
      let env, var = bind_flexible env (fst binding) in
      let t0 = TyOpen var in
      (* And substitute it properly in [e]. *)
      let e = tsubst_expr t0 0 e in
      (* Type-check [e] itself. *)
      let env, x = check_expression env ?annot e in
      (* And notify the user about the choice we made for the flexible variable
       * instantiation. *)
      let name =
        match binding with
        | (User (_, n), _, _), _ -> n
        | _ -> assert false
      in
      may_raise_error env (Instantiated (name, t0));
      env, x

  | ELocalType (group, e) ->
      let env, e, _, _ = bind_data_type_group_in_expr env group e in
      check_expression env e

  (* We assume that [EBigLambdas] is allowed only above [ELambda]. This
     allows us to cheat when handling [EBigLambda]. Instead of introducing a
     fresh type variable [a], synthesizing the type [t] of the body, and
     constructing the abstraction of [a] in [t], we rely on the fact that
     [ELambda] carries a type annotation. This allows us to determine,
     ahead of time, the desired type, so we don't need to implement the
     operation of abstracting [a] in [t]. *)

  | EBigLambdas (vars, e) ->

      (* Build the desired polymorphic function type. Note that we build
         this type without opening or closing any quantifiers. This is the
         trick. *)
      let desired = type_for_function_def expr in
      
      (* Enter the big Lambdas. *)
      let env, { subst_expr; _ } = bind_evars env (List.map fst vars) in
      let e = subst_expr e in

      (* Check that the body is well-typed. *)
      let (sub_env, _ : env * var) = check_expression env e in

      (* In case type-checking the function body instantiated some flexible
       * variables, carry this information over to the environment which we
       * return. This is in line with the subtraction of arrow types. *)
      let env = Permissions.import_flex_instanciations env sub_env in

      (* Return the desired type. This is where we cheat. *)
      return env desired

  | ELambda (arg, return_type, body) ->

      (* We can't create a closure over exclusive variables. Create a stripped
       * environment with only the duplicable parts. *)
      let sub_env = Permissions.keep_only_duplicable env in

      (* Introduce a variable [x] that stands for the function argument. *)
      let sub_env, { subst_expr; vars; _ } = bind_evars sub_env [ fresh_auto_name "arg", KTerm, location sub_env ] in
      (* Its scope is just the function body. *)
      let x = match vars with [ x ] -> x | _ -> assert false in
      let body = subst_expr body in
      (* Assume that we have permission [x @ arg]. *)
      let sub_env = Permissions.add sub_env x arg in

      (* Type-check the function body. *)
      let sub_env, p = check_expression sub_env ~annot:return_type body in

      begin match Permissions.sub sub_env p return_type with
      | Left (_, d) ->
          Log.debug ~level:8 "%a" DerivationPrinter.pderivation d;
          (* Return the desired arrow type. *)
          return env (TyArrow (arg, return_type))
      | Right d ->
          raise_error sub_env (ExpectedType (return_type, p, d))
      end

  | EAssign (e1, field_struct, e2) ->
      let fname = field_struct.SurfaceSyntax.field_name in
      let hint = add_hint hint (Field.print fname) in
      let env, p1 = check_expression env ?hint e1 in
      let env, p2 = check_expression env e2 in
      let success branch k =
        (* Check that this datacon is exclusive. *)
        let flavor = branch.branch_flavor in
        if not (DataTypeFlavor.can_be_written flavor) then
          raise_error env (AssignNotExclusive (TyConcrete branch, snd branch.branch_datacon));

        let branch = replace_field branch fname (fun i _ ->
          field_struct.SurfaceSyntax.field_offset <- Some i;
          TySingleton (TyOpen p2)
        ) in
        k branch (fun env -> return env ty_unit)
      in
      let failure () =
        raise_error env (NoSuchField (p1, fname))
      in
      transform_constructor_permission env p1 success failure

  | EAssignTag (e1, new_datacon, info) ->
      (* Type-check [e1]. *)
      let env, p1 = check_expression env e1 in

      (* Find the ordered list of field names associated with [new_datacon]. *)
      let field_names = fields_for_datacon env new_datacon in

      let success old_branch k =
        let t = TyConcrete old_branch in
        let old_datacon = old_branch.branch_datacon in
        (* The current type should be mutable. *)
        let old_flavor = old_branch.branch_flavor in
        if not (DataTypeFlavor.can_be_written old_flavor) then
          raise_error env (AssignNotExclusive (t, snd old_datacon));

        (* Also, the number of fields should be the same. *)
        if List.length old_branch.branch_fields <> List.length field_names then
          raise_error env (FieldCountMismatch (t, snd new_datacon));

        (* Change the field names. *)
        let branch_fields = List.map2
          (fun field (_, e) -> field, e)
          field_names
          old_branch.branch_fields
        in

        (* XXX jp: I believe this check is incorrect, we need to check that the
         * branch number is the same, not that this is the same data constructor
         * (meaning this would be a very dumb tag update). *)
        if resolved_datacons_equal env old_datacon new_datacon then
          info.SurfaceSyntax.is_phantom_update <- Some true
        else
          info.SurfaceSyntax.is_phantom_update <- Some false;

        (* And don't forget to change the datacon as well. *)
        k { old_branch with
          branch_flavor = flavor_for_datacon env new_datacon;
          branch_datacon = new_datacon;
          branch_fields;
          (* the type of the adoptees does not change *)
        } (fun env -> return env ty_unit)
      in
      let failure () =
        raise_error env (CantAssignTag p1)
      in
      transform_constructor_permission env p1 success failure


  | EAccess (e, field_struct) ->
      let fname = field_struct.SurfaceSyntax.field_name in
      let hint = add_hint hint (Field.print fname) in
      let env, p = check_expression env ?hint e in
      let success branch k =
        match MzList.find_opti (fun i (field, t) ->
          if Field.equal field fname then begin
            field_struct.SurfaceSyntax.field_offset <- Some i;
            Some !!=t
          end else
            None
        ) branch.branch_fields
        with
        | Some p' -> k branch (fun env -> env, p')
        | None -> raise_error env (NoSuchField (p, fname))
      in
      let failure () =
        (* XXX jp: could we give a better error message here *)
        raise_error env (NoSuchField (p, fname))
      in
      transform_constructor_permission env p success failure

  | EApply (e1, e2) ->
      begin match eunloc e1 with
      | EApply _ ->
          may_raise_error env NoMultipleArguments
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
      let env, return_type = check_function_call env ?annot x1 x2 in
      return env return_type

  | ETApply (e, t, k) ->
      let env, x = check_expression env e in
      let rec find_and_instantiate = function
        | TyQ (Forall, (name, k', loc), UserIntroduced, t') as _t0 ->
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
                  (* The trick is: we're not opening the binders that we're
                   * crossing, meaning that we need to "unlift" the instantiated
                   * type to account for the binder that we just destroyed. This
                   * is the reason for the "lift (-1)" above. *)
                  match find_and_instantiate t' with
                  | Some t' ->
                      Some (TyQ (Forall, (name, k', loc), UserIntroduced, t'))
                  | None ->
                      None
                end
            end
        | _ ->
            None
      in
      (* Find something that works. *)
      let t = MzList.find_opt find_and_instantiate (get_permissions env x) in
      let t = match t with
        | Some t ->
            t
        | None ->
            raise_error env (BadTypeApplication x);
      in
      (* And return a fresh var with that new list of permissions. *)
      let name =
        match get_name env x with
        | User (_, x) ->
            Auto (Variable.register (Variable.print x ^ "_inst"))
        | _ as x ->
            x
      in
      let env, x = bind_rigid env (name, KTerm, get_location env x) in
      Permissions.add env x t, x

  | ETuple exprs ->
      (* Propagate type annotations inside the tuple. *)
      let annotations = match annot with
        | Some (TyTuple annotations) when List.length annotations = List.length exprs ->
            List.map (fun x -> Some x) annotations
        | _ ->
            MzList.make (List.length exprs) (fun _ -> None)
      in
      let env, components = MzList.fold_left2i
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
        | Some (TyConcrete branch) ->
            branch.branch_adopts
        | _ ->
            ty_bottom
      in
      let annotations = match annot with
        | Some (TyConcrete branch) ->
            let annots = branch.branch_fields in
            (* Every field in the type annotation corresponds to a field in the
             * expression, i.e. the type annotation makes sense. *)
            if List.for_all (fun (name, _) ->
              List.exists (fun (name', _) ->
                Field.equal name name'
              ) fieldexprs
            ) annots then
              annots
            else
              (* XXX Error here? *)
              []
        | _ ->
            []
      in
      (* Find the corresponding fields. *)
      let fields = fields_for_datacon env datacon in
      (* Take out of the provided fields one of them. *)
      let take env name' l =
        match MzList.take_bool (fun (name, _) -> Field.equal name name') l with
        | Some (l, elt) ->
            snd elt, l
        | None ->
            raise_error env (MissingField name')
      in
      (* Find the annotation for one of the fields. *)
      let annot name =
        MzList.find_opt (function
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

      (* Do the bulk of the work. We're iterating on the _definition_ of the
       * fields to make sure we construct the expression with the fields in the
       * right order, and with all the fields. *)
      let env, remaining, fieldvals = List.fold_left (fun (env, remaining, fieldvals) name ->
        (* Actually we don't care about the expected type for the field. We
         * just want to make sure all fields are provided. *)
        let p, remaining = take env name remaining in
        env, remaining, (name, ty_equals p) :: fieldvals
      ) (env, fieldexprs, []) fields in
      (* Make sure the user hasn't written any superfluous fields. *)
      begin match remaining with
      | (name, _) :: _ ->
          raise_error env (ExtraField name)
      | _ ->
          ()
      end;
      let fieldvals = List.rev fieldvals in
      let branch = {
        branch_flavor = flavor_for_datacon env datacon;
        branch_datacon = datacon;
        branch_fields = fieldvals;
        branch_adopts = clause;
      } in
      return env (TyConcrete branch)


  | EInt _ ->
      return env !*t_int

  | ELocated (e, new_pos) ->
      let old_pos = location env in
      let env = locate env new_pos in
      let env, p = check_expression env ?hint ?annot e in
      locate env old_pos, p

  | EIfThenElse (explain, e1, e2, e3) ->
      let hint_1 = add_hint hint "if" in
      let env, x1 = check_expression env ?hint:hint_1 e1 in

      (* The current convention is that if a data type has two
        constructors, say False | True, then the first one
        means false and the second one means true; i.e., the
        first one will cause the [else] branch to be executed,
        whereas the second one will cause the [then] branch to
        be executed. *)

      let env, (false_t, true_t) =
        match MzList.take_bool (is_data_type_with_two_constructors env) (get_permissions env x1) with
        | Some (stripped_permissions, t) ->
            (* The type that has two constructors should only disappear from the
             * permission list of [x1] if not duplicable. One may ask: how come
             * the merge operation won't re-merge the two constructors into the
             * original, nominal type? Well, if this is a _value_ exported from
             * another module, the [Merge] operation won't touch it, assuming
             * that values exported from other modules won't change (since they
             * now can only be duplicable), so we need to leave the original,
             * duplicable permission here. *)
            let env =
              if FactInference.is_duplicable env t then
                env
              else
                (* Necessarily in our own module, meaning it will be merged
                 * properly. *)
                set_permissions env x1 stripped_permissions
            in
            let split_apply cons args =
              match Option.extract (get_definition env cons) with
              | Concrete [b1; b2] ->
                  let branch1 = instantiate_type b1 args in
                  let branch2 = instantiate_type b2 args in
                  branch1, branch2
              | _ ->
                  assert false
            in
            env, begin match t with
            | TyOpen p ->
                split_apply p []
            | TyApp (cons, args) ->
                split_apply !!cons args
            | TyConcrete _ ->
                t, t
            | _ ->
                Log.error "Contradicts [is_data_type_with_two_constructors]";
            end
        | None ->
            raise_error env (NoTwoConstructors x1);
      in
      (* Here, if the original type was duplicable, we may be doing "x @ bool * x
       * @ True" but [Permissions] knows (I hope) how to simplify that. *)
      let false_env = Permissions.add env x1 false_t in
      let true_env = Permissions.add env x1 true_t in

      (* The control-flow diverges. *)
      let hint_then = add_hint hint "then" in
      let result_then = check_expression true_env ?hint:hint_then ?annot e2 in
      let hint_else = add_hint hint "else" in
      let result_else = check_expression false_env ?hint:hint_else ?annot e3 in

      let dest = Merge.merge_envs env ?annot result_then result_else in

      if explain then
        Debug.explain_merge dest [result_then; result_else];

      dest

  | EMatch (explain, e, patexprs) ->
      let hint = add_hint hint "match" in 
      let env, x = check_expression env ?hint e in

      (* Type-check each branch separately, returning an environment for that
       * branch as well as a var. *)
      let sub_envs = List.map (fun (pat, expr) ->
        let env = refine_perms_in_place_for_pattern env x pat in
        let env, { subst_expr; _ } =
          check_bindings env Nonrecursive [pat, EOpen x]
        in
        let expr = subst_expr expr in
        check_expression env ?annot expr
      ) patexprs in

      (* Combine all of these left-to-right to obtain a single return
       * environment *)
      let dest = MzList.reduce (Merge.merge_envs env ?annot) sub_envs in

      if explain then
        Debug.explain_merge dest sub_envs;

      dest

  | EGive (x, e) ->
      (* Small helper function. *)
      let replace_clause perm clause =
        match perm with
        | TyConcrete branch ->
            assert (is_non_bottom branch.branch_adopts = None); (* the old clause is bottom *)
            TyConcrete { branch with branch_adopts = clause }
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
      begin match MzList.take (has_adopts_clause env) (get_permissions env y) with
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
                  raise_error env (NonExclusiveAdoptee t);
                (* The clause is now [t]. Extract it from the list of available
                 * permissions for [x]. We know it works because we type-checked
                 * the whole [EConstraint] already. *)
                let env = Option.extract (Permissions.sub env x t |> Permissions.drop_derivation) in
                (* Refresh the structural permission for [e], using the new
                 * clause. *)
                let perm = replace_clause perm t in
                let env = set_permissions env y (perm :: remaining_perms) in
                (* We're done. *)
                return env ty_unit
          else begin
            (* Check that the adoptee is exclusive. We do *not* check this when
               we examine an algebraic data type definition that has an adopts
               clause, because it is more flexible to defer this check to actual
               adoption time. Indeed, the type parameters have been instantiated,
               local mode assumptions are available, so the check may succeed here
               whereas it would have failed if performed at type definition time. *)
            if not (FactInference.is_exclusive env clause) then
              raise_error env (NonExclusiveAdoptee clause);
            (* The clause is known. Just take the required permission out of the
             * permissions for x. *)
            match Permissions.sub env x clause |> Permissions.drop_derivation with
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
      begin match MzList.find_opt (has_adopts_clause env) (get_permissions env y) with
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
      (* Check that we have an exclusive permission for [y]. This is a stronger condition
        than strictly required for type soundness (no condition on [y] would be
        enough), but it should allow us to detect a few more programmer errors. *)
      (* TEMPORARY if we have an exclusive permission for [x], then we could
        emit a warning, because in this case [y owns x] is certain to return
        false. *)
      if not (List.exists (FactInference.is_exclusive env) (get_permissions env y)) then
        raise_error env (NoAdoptsClause y);
      return env !*t_bool

  | EExplained e ->
      let env, x = check_expression env ?hint e in
      Debug.explain env ~x;
      (* Log.debug "%a" TypePrinter.penv env;
      if true then failwith "Explanation above"; *)
      env, x

  | EFail ->
      let name = Auto (Variable.register "/inconsistent") in
      let env, x = bind_rigid env (name, KTerm, location env) in
      let env = mark_inconsistent env in
      env, x

  | EBuiltin _ ->
      (* A builtin value is type-checked like [fail], i.e., it has type
        bottom. This is unsafe! The user must know what they are doing.
        Unlike [fail], this does not imply that the code that follows
        is dead, so we do not set [env.inconsistent]. *)
      begin match annot with
      | Some t ->
          return env t
      | None ->
          Log.error "Please annotate your builtins"
      end

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
            | POpen p, (EBigLambdas _ | ELambda _) ->
                let t = type_for_function_def expr in
                Permissions.add env p t
            | _ ->
                raise_error env RecursiveOnlyForFunctions
          ) env expressions patterns
      | Nonrecursive ->
          env
    in
    let env = List.fold_left2 (fun env pat expr ->
      let hint = match pat with
        | POpen p ->
            Some (get_name env p)
        | _ ->
            None
      in
      let env, var = check_expression env ?hint expr in
      let env = unify_pattern env pat var in
      env) env patterns expressions
    in
    env, subst_kit
;;

let check_declaration_group
    (env: env)
    (defs: definitions)
    (toplevel_items: toplevel_item list): env * toplevel_item list * (Variable.name * var) list =
  let p, rec_flag, patexprs = defs in
  let env = locate env p in
  let env, { names; vars; subst_toplevel; _ } = check_bindings env rec_flag patexprs in
  env, subst_toplevel toplevel_items, List.combine names vars
;;
