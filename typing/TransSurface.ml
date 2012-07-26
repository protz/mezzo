(* This module translates the surface syntax down to our internal
   representation.

   - All implicit name bindings made through [TyNameIntro] are turned into
     explicit quantifiers, either [TyForall] or [TyExists].
   - Function parameters that are not consumed, when desugared, generate a
     permission in the returned type. [TyConsumes] annotations are removed.
   - Type annotations in patterns are removed, and are attached to let or val
     bindings instead.
   - Location information inside types and patterns is dropped.
*)

open SurfaceSyntax
open KindCheck
open Utils

module T = Types
module E = Expressions


(* -------------------------------------------------------------------------- *)

(* Types *)

let fold_forall bindings t =
  List.fold_right (fun binding t ->
    T.TyForall (binding, t)
  ) bindings t
;;

let fold_exists bindings t =
  List.fold_right (fun binding t ->
    T.TyExists (binding, t)
  ) bindings t
;;

(* We need to tell the next AST which names are used provided and which are
 * auto-generated. *)
let name_user = fun (x, k, l) -> (T.User x, k, l);;
let name_auto = fun (x, k, l) -> (T.Auto x, k, l);;

(* [strip_consumes env t] removes all the consumes annotations from [t]. A
   [consumes t] annotation is replaced by [=c] with [c] fresh, as well as
   [c @ t] at top-level. The function returns:
   - [t] without its consumes annotations
   - the list of fresh names such as [c]
   - the list of permissions such as [c @ t].
*)
let strip_consumes (env: env) (t: typ): typ * type_binding list * typ list =
  (* I don't think it's worth having a tail-rec function here... this internal
   * function returns pairs of [name * typ], except that permissions that are
   * marked as [consumes] do not allocate a fresh name, so they have no
   * associated name, hence the [Variable.name option]. *)
  let rec strip_consumes (env: env) (t: typ): typ * (Variable.name option * typ * T.location) list  =
    match t with
    | TyLocated (t, p1, p2) ->
        (* Keep the location information, may be useful later on. *)
        let env = locate env p1 p2 in
        let t, acc = strip_consumes env t in
        TyLocated (t, p1, p2), acc

    | TyTuple ts ->
        let ts, accs = List.split (List.map (strip_consumes env) ts) in
        TyTuple ts, List.flatten accs

    | TyConcreteUnfolded (datacon, fields) ->
        let accs, fields = List.fold_left (fun (accs, fields) field ->
          match field with
          | FieldPermission _ ->
              (accs, field :: fields)
          | FieldValue (name, t) ->
              let t, acc = strip_consumes env t in
              (acc :: accs, FieldValue (name, t) :: fields)
        ) ([], []) fields in
        let fields = List.rev fields in
        let acc = List.flatten accs in
        TyConcreteUnfolded (datacon, fields), acc

    | TyNameIntro (x, t) ->
        let t, acc = strip_consumes env t in
        TyNameIntro (x, t), acc

    | TyBar (t, p) ->
        (* Strip all consumes annotations from [t]. *)
        let t, acc = strip_consumes env t in
        (* Get the permissions contained in [p] as a list. *)
        let perms = flatten_star p in
        (* Some of them are consumed, and should be returned in the accumulator
         * of consumed permissions. Others are kept. *)
        let consumed, kept =
          List.partition (function TyConsumes _ -> true | _ -> false) perms
        in
        let consumed =
          List.map (function TyConsumes p -> None, p, env.location | _ -> assert false) consumed
        in
        let p = fold_star kept in
        (* Minimal cleanup. *)
        (if List.length kept > 0 then TyBar (t, p) else t),
        acc @ consumed

    | TyConsumes t ->
        let name = Variable.register (fresh_name "/c") in
        let perm = TyAnchoredPermission (TyVar name, t) in
        ty_equals name, [Some name, perm, env.location]

    | TyUnknown
    | TyDynamic
    | TyVar _
    | TySingleton _
    (* These are opaque, no consumes annotations inside of these. *)
    | TyForall _
    | TyApp _
    | TyArrow _ ->
        t, []

    (* Permissions *)
    | TyAnchoredPermission _
    | TyEmpty
    | TyStar _ ->
        Log.error "[KindCheck] made sure there are no unwanted permissions here, and \
          the right-hand side of a [TyBar] gets a special treatment in [TyBar]." 

  in
  let t, name_perms = strip_consumes env t in
  let names, perms, locations = Hml_List.split3 name_perms in
  let names = Hml_List.filter_some names in
  let bindings = List.map2 (fun x loc -> x, KTerm, loc) names locations in
  t, bindings, perms
;;


let rec translate_type (env: env) (t: typ): T.typ =
  match t with
  | TyLocated (t, p1, p2) ->
      translate_type (locate env p1 p2) t

  | TyTuple ts ->
      T.TyTuple (List.map (translate_type env) ts)

  | TyUnknown ->
      T.TyUnknown

  | TyDynamic ->
      T.TyDynamic

  | TyEmpty ->
      T.TyEmpty

  | TyVar x ->
      let _, index = find x env in
      T.TyVar index

  | TyConcreteUnfolded branch ->
      T.TyConcreteUnfolded (translate_data_type_def_branch env branch)

  | TySingleton t ->
      T.TySingleton (translate_type env t)

  | TyApp (t1, t2) ->
      T.TyApp (translate_type env t1, translate_type env t2)

  | TyArrow (t1, t2) ->
      let universal_bindings, t1, t2 = translate_arrow_type env t1 t2 in
      let arrow = T.TyArrow (t1, t2) in
      fold_forall universal_bindings arrow

  | TyForall ((x, k, loc), t) ->
      let env = bind env (x, k) in
      T.TyForall ((T.User x, k, loc), translate_type env t)

  | TyAnchoredPermission (t1, t2) ->
      T.TyAnchoredPermission (translate_type env t1, translate_type env t2)

  | TyStar (t1, t2) ->
      T.TyStar (translate_type env t1, translate_type env t2)

  | TyNameIntro (x, t) ->
      (* [x: t] translates into [(=x | x@t)] -- with [x] bound somewhere above
         us. *)
      let _, index = find x env in
      T.TyBar (
        T.TySingleton (T.TyVar index),
        T.TyAnchoredPermission (T.TyVar index, translate_type env t)
      )

  | TyConsumes _ ->
      (* These should've been removed by [strip_consumes]. *)
      illegal_consumes env

  | TyBar (t1, t2) ->
      T.TyBar (translate_type env t1, translate_type env t2)


and translate_data_type_def_branch (env: env) (branch: data_type_def_branch): T.data_type_def_branch =
  let datacon, fields = branch in
  let fields = List.map (function
    | FieldValue (name, t) ->
        T.FieldValue (name, translate_type env t)
    | FieldPermission t ->
        T.FieldPermission (translate_type env t)
  ) fields in
  datacon, fields

and translate_arrow_type env t1 t2 =

  (* Get the implicitly quantified variables in [t1]. These will be
     quantified as universal variables above the arrow type. *)
  let t1_bindings = names env t1 in

  (* This is the procedure that removes the consumes annotations. It is
   * performed in the surface syntax. The first step consists in carving out
   * the [consumes] annotations, replacing them with [=c]. *)
  let t1, perm_bindings, perms = strip_consumes env t1 in

  (* Now we give a name to [t1] so that we can speak about the argument in
   * the returned type. Note: this variable name is not lexable, so no risk
   * of conflict. *)
  let root = Variable.register (fresh_name "/root") in
  let root_binding = root, KTerm, (tloc t1) in

  (* We now turn the argument into (=root | root @ t1 ∗ c @ … ∗ …) with [t1]
   * now devoid of any consumes annotations. *)
  let fat_t1 = TyBar (
    ty_equals root,
    fold_star (TyAnchoredPermission (TyVar root, t1) :: perms)
  ) in

  (* So that we don't mess up, we use unique names in the surface syntax and
   * let the translation phase do the proper index computations. *)
  let universal_bindings = t1_bindings @ perm_bindings @ [root_binding] in
  let env = List.fold_left (fun env (x, k, _) -> bind env (x, k)) env universal_bindings in
  let fat_t1 = translate_type env fat_t1 in

  (* The return type can also bind variables with [x: t]. These are
   * existentially quantified. *)
  let t2_bindings = names env t2 in

  (* We need to return the original permission on [t1], minus the components
   * that were consumed: these have been carved out of [t1] by
   * [strip_consumes]. *)
  let t2 = TyBar (
    t2,
    TyAnchoredPermission (TyVar root, t1)
  ) in
  let env = List.fold_left (fun env (x, k, _) -> bind env (x, k)) env t2_bindings in

  (* Build the resulting type. *)
  let t2 = translate_type env t2 in
  let t2 = fold_exists (List.map name_user t2_bindings) t2 in

  (* Finally, translate the universal bindings as well. *)
  let universal_bindings =
    List.map name_user t1_bindings @
    List.map name_auto perm_bindings @
    List.map name_auto [root_binding]
  in
  universal_bindings, fat_t1, t2
;;


let translate_abstract_fact (params: Variable.name list) (fact: abstract_fact option): T.fact =
  match fact with
  | None ->
      T.Affine
  | Some (FExclusive _) ->
      T.Exclusive
  | Some (FDuplicableIf (ts, _)) ->
      (* [KindCheck] already made sure these are just names _and_ they're valid. *)
      let names = List.map (function TyVar name -> name | _ -> assert false) ts in
      let arity = List.length params in
      let bitmap = Array.make arity false in
      List.iter (fun name ->
        let i = Hml_List.index name params in
        bitmap.(i) <- true
      ) names;
      T.Duplicable bitmap
;;

let translate_data_type_def (env: env) (data_type_def: data_type_def) =
  match data_type_def with
  | Concrete (flag, (name, params), branches) ->
      let params = List.map (fun (x, k, _) -> x, k) params in
      (* Add the type parameters in the environment. *)
      let env = List.fold_left bind env params in
      (* Translate! *)
      let branches = List.map (translate_data_type_def_branch env) branches in
      (* This fact will be refined later on. *)
      let arity = List.length params in
      let fact = match flag with
        | Exclusive -> T.Exclusive
        | Duplicable -> T.Duplicable (Array.make arity false)
      in
      (* This is conservative but the variance inference will take care of
       * setting the right values for the variance of the parameters. *)
      let variance = Hml_List.make arity (fun _ -> T.Invariant) in
      name, (Some (flag, branches), variance), fact, karrow params KType
  | Abstract ((name, params), kind, fact) ->
      let params = List.map (fun (x, k, _) -> x, k) params in
      let fact = translate_abstract_fact (fst (List.split params)) fact in
      (* TODO: add +, -, and = syntax in the parser to annotate in abstract type
       * definitions some parameters as being co, contra, or bi-variant. *)
      let variance = Hml_List.make (List.length params) (fun _ -> T.Invariant) in
      name, (None, variance), fact, karrow params kind
;;


(* [translate_data_type_group env tenv data_type_group] returns [env, tenv, points] where:
  - the type definitions have been added with the corresponding levels in [env]
  - type definitions have been desugared and added to [tenv]; the types have been
    opened inside the branches,
  - the points corresponding to the various types are in [points]; the item at
    index i has level i (the list is in order)
*)
let translate_data_type_group
    (env: env)
    (tenv: T.env)
    (data_type_group: data_type_group): env * T.env * T.point list
  =

  let bindings = bindings_data_type_group data_type_group in

  (* We're recycling the environments from [SurfaceSyntax] because we're lazy.
   * We don't really need the [Types.kind] information here, but all the other
   * functions such as [bind] and [find] are defined already. *)
  let env = List.fold_left (bind ~strict:()) env bindings in 

  (* First do the translation pass. *)
  let translated_definitions: (Variable.name * T.type_def * T.fact * T.kind) list =
    List.map (translate_data_type_def env) data_type_group
  in

  (* Then build up the resulting environment. *)
  let tenv, points = List.fold_left (fun (tenv, acc) (name, def, fact, kind) ->
    let name = T.User name in
    let tenv, point = T.bind_type tenv name tenv.T.location ~definition:def fact kind in
    tenv, point :: acc) (tenv, []
  ) translated_definitions in
  let points = List.rev points in

  (* Construct the reverse-map from constructors to points. *)
  let tenv = List.fold_left2 (fun tenv (_, def, _, _) point ->
    match def with
    | None, _ ->
        tenv
    | Some (_, def), _ ->
        let type_for_datacon = List.fold_left (fun type_for_datacon (name, _) ->
          T.DataconMap.add name point type_for_datacon
        ) tenv.T.type_for_datacon def in  
        { tenv with T.type_for_datacon }
  ) tenv translated_definitions points in

  (* Finally, open the types in the type definitions themselves. *)
  let total_number_of_data_types = List.length points in
  let tenv = T.fold_types tenv (fun tenv point { T.kind; _ } { T.definition; _ } ->
    match definition with
    | Some (None, _) ->
        (* It's an abstract type, it has no branches where we should perform the
         * opening. *)
        tenv

    | Some (Some (flag, branches), variance) ->
        let arity = T.get_arity_for_kind kind in

        (* Replace each TyVar with the corresponding TyPoint, for all branches. *)
        let branches = Hml_List.fold_lefti (fun level branches point ->
          (* We need to add [arity] because one has to move up through the type
           * parameters to reach the typed defined at [level]. *)
          let index = total_number_of_data_types - level - 1 + arity in
          (* Perform the substitution. *)
          List.map
            (T.tsubst_data_type_def_branch (T.TyPoint point) index)
            branches
        ) branches points in

        (* And replace the corresponding definition in [tenv]. *)
        T.replace_type tenv point (fun binder ->
          { binder with T.definition = Some (Some (flag, branches), variance) }
        )

    | None ->
        Log.error "There should be only type definitions at this stage"
  ) tenv in

  (* Return both environments and the list of points. *)
  env, tenv, points
;;


(* -------------------------------------------------------------------------- *)

(* Patterns *)

let clean_pattern env pattern =
  let rec pattern_to_type env = function
    | PVar x ->
        TyVar x
    
    | PTuple patterns ->
        TyTuple (List.map (pattern_to_type env) patterns)

    | PConstruct (name, fieldpats) ->
        let fieldtypes = List.map (fun (field, pat) ->
          FieldValue (field, pattern_to_type env pat)) fieldpats
        in
        TyConcreteUnfolded (name, fieldtypes)

    | PLocated (p, _, _) ->
        pattern_to_type env p

    | PConstraint _ ->
        Log.error "[clean_pattern] should've been called on that type before!"
  in
  let rec clean_pattern env = function
    | PVar _ as pattern ->
        pattern, []

    | PTuple patterns ->
        let patterns, assertions = List.split (List.map (clean_pattern env) patterns) in
        PTuple patterns, List.flatten assertions

    | PConstruct (name, fieldpats) ->
        let fieldpats, assertions = List.fold_left
          (fun (fieldpats, assertions) (field, pat) ->
            let pat, assertion = clean_pattern env pat in
            (field, pat) :: fieldpats, assertion :: assertions)
          ([], []) fieldpats
        in
        let fieldpats = List.rev fieldpats in
        PConstruct (name, fieldpats), List.flatten assertions

    | PConstraint (pattern, typ) ->
        let pattern, assertions = clean_pattern env pattern in
        if List.length assertions > 0 then
          Log.warn "%a there are nested type annotations in this pattern, the \
            nested parts may end up being asserted twice, even though they may \
            not be duplicable"
            Lexer.p env.location;
        let assertion = TyAnchoredPermission (pattern_to_type env pattern, typ) in
        pattern, assertion :: assertions

    | PLocated (pattern, p1, p2) ->
        let pattern, assertion = clean_pattern (locate env p1 p2) pattern in
        PLocated (pattern, p1, p2), assertion
  in
  let pattern, assertions = clean_pattern env pattern in
  pattern, List.rev assertions
;;


let rec translate_pattern env = function
  | PVar x ->
      E.PVar (x, env.location)
  | PTuple ps ->
      E.PTuple (List.map (translate_pattern env) ps)
  | PConstruct (name, fieldpats) ->
      let fields, pats = List.split fieldpats in
      let pats = List.map (translate_pattern env) pats in
      E.PConstruct (name, List.combine fields pats)
  | PLocated (p, p1, p2) ->
      translate_pattern (locate env p1 p2) p
  | PConstraint _ ->
        Log.error "[clean_pattern] should've been called on that type before!"
;;


(* -------------------------------------------------------------------------- *)

(* Expressions *)

let rec translate_expr (env: env) (expr: expression): E.expression =
  match expr with
  | EConstraint (e, t) ->
      let e = translate_expr env e in
      let t = translate_type env t in
      E.EConstraint (e, t)

  | EVar x ->
      let _, index = find x env in
      E.EVar index

  | ELet (flag, patexprs, body) ->
      let env, patexprs, assertions = translate_patexprs env flag patexprs in
      let body = translate_expr env body in
      let body =
        if List.length assertions > 0 then
          let assertions = fold_star assertions in
          let assertions = translate_type env assertions in
          E.e_assert assertions body
        else
          body
      in
      E.ELet (flag, patexprs, body)

  | EFun (vars, arg, return_type, body) ->

      (* Introduce all universal bindings. *)
      let env = List.fold_left (fun env (x, k, _) -> bind env (x, k)) env vars in

      (* Translate the function type. *)
      let universal_bindings, arg, return_type =
        translate_arrow_type env arg return_type
      in

      (* Introduce all other bindings in scope *)
      let env = List.fold_left (fun env -> function
        | (T.Auto x, k, _) | (T.User x, k, _) -> bind env (x, k)
      ) env universal_bindings in

      (* Now translate the body (which will probably refer to these bound
       * names). *)
      let body = translate_expr env body in
      let vars = List.map name_user vars in
      E.EFun (vars @ universal_bindings, arg, return_type, body)

  | EAssign (e1, x, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EAssign (e1, x, e2)

  | EAccess (e, x) ->
      let e = translate_expr env e in
      E.EAccess (e, x)

  | EAssert t ->
      let t = translate_type env t in
      E.EConstraint (E.e_unit, T.TyBar (T.ty_unit, t))

  | EApply (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EApply (e1, e2)

  | EMatch (b, e, patexprs) ->
      let e = translate_expr env e in
      let patexprs = List.map (fun (pat, expr) ->
        (* Extract assertions from the pattern. *)
        let pat, assertions = clean_pattern env pat in
        (* Collect the names. *)
        let names = bindings_pattern pat in
        (* Translate the pattern. *)
        let pat = translate_pattern env pat in
        (* Bind the names for further translating, and don't forget to include
         * assertions in the translation as well. *)
        let sub_env = List.fold_left bind env names in
        let expr = translate_expr sub_env expr in
        let expr =
          if List.length assertions > 0 then
            let assertions = translate_type env (fold_star assertions) in
            E.e_assert assertions expr
          else
            expr
        in
        pat, expr) patexprs
      in
      E.EMatch (b, e, patexprs)

  | ETuple expressions ->
      E.ETuple (List.map (translate_expr env) expressions)

  | EConstruct (name, fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, translate_expr env expr) fieldexprs
      in
      E.EConstruct (name, fieldexprs)

  | EIfThenElse (b, e1, e2, e3) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      E.EIfThenElse (b, e1, e2, e3)

  | ESequence (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.(ELet (Nonrecursive, [p_unit, e1], e2))

  | ELocated (e, p1, p2) ->
      let e = translate_expr env e in
      E.ELocated (e, p1, p2)

  | EPlus (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EPlus (e1, e2)

  | EMinus (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EMinus (e1, e2)

  | ETimes (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.ETimes (e1, e2)

  | EDiv (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EDiv (e1, e2)

  | EUMinus e ->
      let e = translate_expr env e in
      E.EUMinus e

  | EInt i ->
      E.EInt i

  | EExplained e ->
      let e = translate_expr env e in
      E.EExplained e

(* This function desugars a list of [pattern * expression] and returns the
 * desugared version, as well as a list of assertions (read: types with kind
 * PERM) that should be enforced later on when the names in the patterns have
 * been bound (typically, below). The assertions are returned as surface syntax. *)
and translate_patexprs
      (env: env)
      (flag: rec_flag)
      (pat_exprs: (pattern * expression) list): env * E.patexpr list * typ list
    =
  let patterns, expressions = List.split pat_exprs in
  (* Remove all inner type annotations and transform them into a list of
   * assertions. *)
  let patterns, assertions = List.fold_left (fun (patterns, assertions) pattern ->
    let pattern, assertion = clean_pattern env pattern in
    pattern :: patterns, assertion :: assertions) ([], []) patterns
  in
  (* Keep the assertions in order as well so as to enforce readability. *)
  let patterns = List.rev patterns and assertions = List.rev assertions in
  (* Find names in patterns. *)
  let names = List.flatten (List.map bindings_pattern patterns) in
  (* Translate the patterns. *)
  let patterns = List.map (translate_pattern env) patterns in
  (* Bind all the names in the sub-environment. *)
  let sub_env = List.fold_left bind env names in
  (* Translate the expressions. *)
  let expressions = match flag with
    | Recursive -> List.map (translate_expr sub_env) expressions
    | Nonrecursive -> List.map (translate_expr env) expressions
  in
  sub_env, List.combine patterns expressions, List.flatten assertions
;;


let open_type_definitions (points: T.point list) (declarations: E.declaration_group) =
  let total_number_of_data_types = List.length points in
  let subst_decl = fun declarations ->
    Hml_List.fold_lefti (fun level declarations point ->
      let index = total_number_of_data_types - level - 1 in
      E.tsubst_decl (T.TyPoint point) index declarations
    ) declarations points
  in
  subst_decl declarations
;;


let translate_declaration_group (env: env) (decls: declaration_group): E.declaration_group =
  let _env, decls = List.fold_left (fun (env, acc) decl ->
    match decl with
    | DLocated (DMultiple (flag, pat_exprs), p1, p2) ->
        let env = locate env p1 p2 in
        let env, pat_exprs, assertions = translate_patexprs env flag pat_exprs in
        let decl = E.DLocated (E.DMultiple (flag, pat_exprs), p1, p2) in
        (* Generate an extra declaration that enforces the type annotations. *)
        let extra =
          if List.length assertions > 0 then
            let assertions = List.map (translate_type env) assertions in
            let open E in
            let open T in
            (* val () = (): (| assertions) *)
            Some (DLocated (DMultiple (Nonrecursive, [
              p_unit, EConstraint (e_unit, TyBar (ty_unit, fold_star assertions))
            ]), p1, p2))
          else
            None
        in
        env, extra :: (Some decl) :: acc
    | _ ->
        Log.error "The structure of declarations is supposed to be very simple"
  ) (env, []) decls in
  List.rev (Hml_List.filter_some decls)
;;


(* [translate env program] returns [env, decls] where:
  - type definitions from [program] have been added to the table of type
    definitions in [env] _and_ opened in both the type definitions themselves
    and [decls], which means all references to these types through [TyVar]s have
    been replaced by [TyPoint]s
  - [decls] is the desugared version of the original declarations; type
    definitions have been opened in there as well.
*)
let translate (tenv: T.env) (program: program): T.env * E.declaration_group =
  (* TEMPORARY we should probably accept an [env] here so that we can safely
   * compose this operation accross files... *)
  let data_type_group, declaration_group = program in
  (* This will just desugar the data type definitions, fill [tenv] with the
   * desugared definitions, an return a list of [points] so that we can
   * perform the substitution in the expressions once we've desugared them. *)
  let env, tenv, points = translate_data_type_group empty tenv data_type_group in
  (* Desugar the definitions. *)
  let declarations = translate_declaration_group env declaration_group in
  (* Perform the required substitutions. *)
  let declarations = open_type_definitions points declarations in
  (* And return everything. *)
  tenv, declarations
;;
