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

open Kind
open SurfaceSyntax
open KindCheck
open KindCheckGlue
open Utils

module T = TypeCore
module E = Expressions

(* -------------------------------------------------------------------------- *)

(* We wish to record which names are user-provided and which are
 * auto-generated. *)
let name_user = fun env (x, k, l) -> (T.User (module_name env, x), k, l);;
let name_auto = fun (x, k, l) -> (T.Auto x, k, l);;

(* [tvar] transforms [v] into a type variable in the internal syntax. *)
let tvar v : T.typ =
  match v with
  |    Local v -> T.TyBound v
  | NonLocal v -> T.TyOpen  v

(* [evar] transforms [v] into an expression variable in the internal syntax. *)
let evar v =
  match v with
  |    Local v -> E.EVar  v
  | NonLocal v -> E.EOpen v

let resolve_datacon env dref =
  let v, datacon = KindCheck.resolve_datacon env dref in
  tvar v, datacon

(* -------------------------------------------------------------------------- *)

let rec conjunction cs ty =
  match cs with
  | [] ->
      ty
  | c :: cs ->
      conjunction cs (TyAnd (c, ty))

let top = function
  | KType ->
      T.TyUnknown
  | KPerm ->
      T.TyEmpty
  | _ ->
      assert false

let twice x kind =
  x, x, kind

let auto_tyq q binding ty =
  T.TyQ (q, name_auto binding, AutoIntroduced, ty)

(* TEMPORARY maybe try to preserve sharing when there is no consumes *)

let rec translate_type env (ty : typ) : T.typ * T.typ * kind =
  match ty with

  | TyLocated (ty, loc) ->
      translate_type (locate env loc) ty

  | TyConsumes ty ->
      (* First, translate [ty]. *)
      let ty1, _, kind = translate_type env ty in
      (* Construct a version of this type where everything is kept, *)
      ty1,
      (* and a version of this type where everything is lost. *)
      top kind,
      (* Also return the kind. *)
      kind

  | TyTuple tys ->
      let tys1, tys2 = MzList.split_map (fun ty ->
        let ty1, ty2, _ = translate_type env ty
        in ty1, ty2
      ) tys in
      T.TyTuple tys1, T.TyTuple tys2, KType

  | TyUnknown ->
      twice T.TyUnknown KType

  | TyDynamic ->
      twice T.TyDynamic KType

  | TyEmpty ->
      twice T.TyEmpty KPerm

  | TyVar x ->
      twice (tvar (find_variable env x)) (find_kind env x)

  | TyConcrete ((dref, fields), clause) ->
      let fields1, fields2 = MzList.split_map (translate_field env) fields in
      let branch1 = {
        T.branch_flavor = ();
        T.branch_datacon = resolve_datacon env dref;
        T.branch_fields = fields1;
        T.branch_adopts = translate_adopts_clause env clause
      } in
      let branch2 = {
        branch1 with
        T.branch_fields = fields2
      } in
      T.TyConcrete branch1, T.TyConcrete branch2, KType

  | TySingleton ty ->
      let ty, _ = translate_type_reset env ty in
      twice (T.TySingleton ty) KType

  | TyApp (ty1, ty2s) ->
      let ty1, kind1 = translate_type_reset env ty1 in
      let ty2s, _ = MzList.split_map (translate_type_reset env) ty2s in
      let _, kind = as_arrow kind1 in
      twice (T.TyApp (ty1, ty2s)) kind

  | TyArrow (domain, codomain) ->
      let bindings, domain, codomain =
        translate_arrow_type env domain codomain
      in
      (* Build a translated function type. *)
      let ty = T.TyArrow (domain, codomain) in
      (* Add the universal quantifiers. *)
      let ty = List.fold_right (auto_tyq T.Forall) bindings ty in
      (* Done. *)
      twice ty KType

  | TyForall (binding, ty) ->
      translate_quantified_type env T.Forall binding ty

  | TyExists (binding, ty) ->
      translate_quantified_type env T.Exists binding ty

  | TyAnchoredPermission (ty1, ty2) ->
      let ty1, _ = translate_type_reset env ty1 in
      let ty2, _ = translate_type_reset env ty2 in
      twice (T.TyAnchoredPermission (ty1, ty2)) KPerm

  | TyStar (p, q) ->
      let p1, p2, _ = translate_type env p in
      let q1, q2, _ = translate_type env q in
      T.TyStar (p1, q1), T.TyStar (p2, q2), KPerm

  | TyNameIntro (x, ty) ->
      (* In principle, [x] has already been bound in the environment.
         The translation of this type is [(=x | x @ ty)]. *)
      let x = tvar (find_variable env (Unqualified x)) in
      let ty1, ty2, _ = translate_type env ty in
      T.TyBar (T.TySingleton x, T.TyAnchoredPermission (x, ty1)),
      T.TyBar (T.TySingleton x, T.TyAnchoredPermission (x, ty2)),
      KType

  | TyBar (ty, p) ->
      let ty1, ty2, _ = translate_type env ty in
      let p1, p2, _ = translate_type env p in
      T.TyBar (ty1, p1), T.TyBar (ty2, p2), KType

  | TyAnd (c, ty) ->
      let c = translate_mode_constraint env c in
      let ty1, ty2, _ = translate_type env ty in
      T.TyAnd (c, ty1), T.TyAnd (c, ty2), KType

  | TyImply (c, ty) ->
      translate_implication env [c] ty

and translate_arrow_type env domain codomain =
  (* Bind a fresh variable to stand for the root of the function
     argument. Bind the names introduced in the left-hand side. *)
  let root = fresh_var "/root" in
  let bindings = (root, KTerm, location env) :: names domain in
  (* Extend the environment with these bindings, so that we can
     translate [domain] and [codomain] and construct the body of
     the desired universal type. *)
  let env = extend env bindings in
  let root = tvar (find_variable env (Unqualified root)) in
  (* Translate the left-hand side. We obtain [domain1], which
     represents the domain with the [consumed] components, and
     [domain2], which represents the domain without them. *)
  let domain1, domain2, _ = translate_type env domain in
  (* Translate the right-hand side. *)
  let codomain, _ = translate_type_reset env codomain in
  let domain = 
    (* The domain is (=root | root @ domain1). *)
    T.TyBar (T.TySingleton root, T.TyAnchoredPermission (root, domain1))
  in
  let domain = Hoist.hoist TypeCore.empty_env domain in
  let codomain =
    (* The codomain is (codomain | root @ domain2). *)
    T.TyBar (codomain, T.TyAnchoredPermission (root, domain2))
  in
  let codomain = Hoist.hoist TypeCore.empty_env codomain in
  bindings, domain, codomain

and translate_type_reset env ty : T.typ * kind =
  (* Gather and bind the names introduced within [ty]. *)
  let bindings = names ty in
  let env = extend env bindings in
  (* Translate [ty]. There should be no [consumes] annotations, so the
     two types that are returned by this call are identical. *)
  let ty, _, kind = translate_type env ty in
  (* Build a series of existential quantifiers. *)
  let ty = List.fold_right (auto_tyq T.Exists) bindings ty in
  ty, kind

and translate_type_reset_no_kind env t : T.typ =
  fst (translate_type_reset env t)

and translate_field env = function
  | FieldValue (f, ty) ->
      (* No [reset] here. *)
      let ty1, ty2, _ = translate_type env ty in
      T.FieldValue (f, ty1), T.FieldValue (f, ty2)
  | FieldPermission ty ->
      let ty1, ty2, _ = translate_type env ty in
      T.FieldPermission ty1, T.FieldPermission ty2

and translate_adopts_clause env = function
  | None ->
      T.ty_bottom
  | Some ty ->
      translate_type_reset_no_kind env ty

(* TEMPORARY merge TyForall/TyExists in the surface syntax *)
and translate_quantified_type env q binding ty =
  let env = extend env [ binding ] in
  let ty, kind = translate_type_reset env ty in
  let ty = T.TyQ (q, name_user env binding, UserIntroduced, ty) in
  twice ty kind

and translate_mode_constraint env (m, ty) =
  m, translate_type_reset_no_kind env ty

and translate_implication env (cs : mode_constraint list) = function
  | TyArrow (ty1, ty2) ->
      (* An implication above an arrow is turned into a conjunction in
        the left-hand side of the arrow. This is done on the fly, just
        before the translation, as a rewriting of the surface syntax to
        itself. (Doing it just after the translation would be more
        problematic, as the translation of arrows introduces quantifiers.) *)
      translate_type env (TyArrow (conjunction cs ty1, ty2))
  | TyImply (c, ty) ->
      (* Multiple implications above an arrow are allowed. *)
      translate_implication env (c :: cs) ty
  | TyLocated (ty, _) ->
      translate_implication env cs ty
  | _ ->
      implication_only_on_arrow env

(* -------------------------------------------------------------------------- *)

let rec translate_data_type_def_branch
    (env: env)
    (flavor: DataTypeFlavor.flavor)
    (adopts: typ option)
    (branch: Datacon.name * data_field_def list)
  : T.unresolved_branch =
  let datacon, fields = branch in
  {
    T.branch_flavor = flavor;
    T.branch_datacon = datacon;
    T.branch_fields = translate_fields env fields;
    T.branch_adopts = translate_adopts env adopts
  }

and translate_adopts env (adopts : typ option) =
  match adopts with
  | None ->
      TypeCore.ty_bottom
  | Some t ->
      translate_type_reset_no_kind env t

and translate_fields env fields =
  List.map (function
    | FieldValue (name, t) ->
        T.FieldValue (name, translate_type_reset_no_kind env t)
    | FieldPermission t ->
        let t, _, _ = translate_type env t in
        T.FieldPermission t
  ) fields

;;

let rec tunloc = function
  | TyLocated (t, _) ->
      tunloc t
  | _ as t ->
      t
;;

let translate_single_fact (params: type_binding list) (accu: Fact.fact) (fact: single_fact) : Fact.fact =
  (* We have an implication. *)
  let Fact (hypotheses, goal) = fact in
  (* We ignore the type in the goal. [KindCheck] has already checked
     that it is the abstract data type that is being declared. *)
  let (mode, _) = goal in
  (* Turn the hypotheses into a map of parameters to modes. Again,
     [KindCheck] has already checked that every type [t] that appears
     in the hypotheses is a parameter. *)
  let open Fact in
  let hs =
    List.fold_left (fun hs (mode, t) ->
      let name =
       match tunloc t with
        | TyVar (Unqualified name) -> name
        | _ -> assert false
      in
      let p : parameter = MzList.index (fun (x, _, _) -> Variable.equal name x) params in
      (* We compute a meet of [previous_mode] and [mode], so that if
        several hypotheses bear on a single parameter, they will be
        correctly taken into account. *)
      let previous_mode =
       try ParameterMap.find p hs with Not_found -> Mode.top
      in
      ParameterMap.add p (Mode.meet previous_mode mode) hs
    ) ParameterMap.empty hypotheses
  in
  (* We now have an implication, [hs => mode], which we wish to add
     to the accumulator [accu]. [KindCheck] has already ensured that
     distinct implications have distinct modes in their heads, so we
     can add this implication. *)
  assert (not (Mode.ModeMap.mem mode accu));
  Mode.ModeMap.add mode (HConjunction hs) accu

let translate_fact (params: type_binding list) (fact: single_fact list): Fact.fact =
  (* Starting with an empty mode map, translate each implication.
     This yields an incomplete mode map, which we complete. *)
  Fact.complete (
    List.fold_left (translate_single_fact params) Mode.ModeMap.empty fact
  )

let translate_data_type_def (env : env) (def : data_type_def) =
  let loc = location env in
  let (name, _, _), annotated_params = def.lhs in
  let variance, params = List.split annotated_params in
  let env = extend env params in
  let _, kind, _ = binding_of_lhs def.lhs in
  match def.rhs with
  | Concrete (flavor, branches, adopts_clause) ->
      (* Translate! The flavor and adopts clause are distributed to every branch. *)
      let branches = List.map (translate_data_type_def_branch env flavor adopts_clause) branches in
      (* This fact will be refined later on. *)
      let fact = Fact.bottom in
      (* We store the annotated variance here. [Variance.analyze_data_types] will
        take care of checking it against the actual variance. *)
      T.({ data_name = name;
        data_location = loc;
        data_definition = Concrete branches;
        data_variance = variance;
        data_fact = fact;
        data_kind = kind
      })
  | Abstract fact ->
      let fact = translate_fact params fact in
      T.({ data_name = name;
        data_location = loc;
        data_definition = Abstract;
        data_variance = variance;
        data_fact = fact;
        data_kind = kind
      })
  | Abbrev t ->
      (* Same remarks for fact/variance as with the Concrete case. *)
      let fact = Fact.bottom in
      T.({ data_name = name;
        data_location = loc;
        data_definition = Abbrev (translate_type_reset_no_kind env t);
        data_variance = variance;
        data_fact = fact;
        data_kind = kind
      })
;;


(* [translate_data_type_group extend env tenv data_type_group] returns [env, group] where:
  - the type definitions have been added with the corresponding levels in [env]
  - type definitions have been desugared into [group].
  The [extend] parameter is normally [KindCheck.extend], but [Interfaces] supplies
  a different function.
*)
let translate_data_type_group
    (extend: env -> type_binding list -> env)
    (env: env)
    (data_type_group: data_type_group)
  : env * T.data_type_group
  =

  let loc, rec_flag, data_type_group = data_type_group in

  let bindings = bindings_data_group_types data_type_group in
  (* The check for duplicate names has been performed already. *)

  (* We're recycling the environments from [SurfaceSyntax] because we're lazy.
   * We don't really need the [Types.kind] information here, but all the other
   * functions such as [bind] and [find] are defined already. *)
  let sub_env = extend env bindings in

  (* Also bind the constructors. *)
  let env = locate env loc in
  let sub_env = bind_data_group_datacons sub_env data_type_group in

  (* First do the translation pass. *)
  let translated_definitions: T.data_type_group = {
    T.group_recursive = rec_flag;
    group_items =
      let sub_env = if rec_flag = Recursive then sub_env else env in
      List.map (translate_data_type_def sub_env) data_type_group
  } in

  (* Return both the environment and the desugared definitions. *)
  sub_env, translated_definitions
;;

          (* TEMPORARY there is some code duplication between here and
             [KindCheck.check_implementation] *)

(* -------------------------------------------------------------------------- *)

(* Patterns *)

(* [clean_pattern] takes a pattern, and removes type annotations from it,
 * constructing a top-level type where "holes" have been replaced by
 * [TyUnknown]s. (x: τ, y) will be cleaned up into (x, y) and (τ, TyUnknown) *)
let clean_pattern pattern =
  let rec clean_pattern loc = function
    | PVar _ as pattern ->
        pattern, TyUnknown

    | PTuple patterns ->
        let patterns, annotations = MzList.split_map (clean_pattern loc) patterns in
        PTuple patterns,
        if List.exists ((<>) TyUnknown) annotations then
          TyTuple annotations
        else
          TyUnknown

    | PConstruct (name, fieldpats) ->
        let fields, pats, annotations = MzList.split3 (List.map
          (fun (field, pat) ->
            let pat, annotation = clean_pattern loc pat in
            field, pat, annotation
          ) fieldpats)
        in
        PConstruct (name, List.combine fields pats),
        if List.exists ((<>) TyUnknown) annotations then
          TyConcrete ((name, List.map2 (fun field t -> FieldValue (field, t)) fields annotations), None)
        else
          TyUnknown

    | PConstraint (pattern, typ) ->
        let pattern, annotation = clean_pattern loc pattern in
        if annotation <> TyUnknown then
          (* TODO provide a real error reporting mechanism for this module *)
          Log.warn "%a nested type annotations are forbidden" Lexer.p loc;
        pattern, typ

    | PAs (pattern, var) ->
        let pattern, annotation = clean_pattern loc pattern in
        PAs (pattern, var), annotation

    | PLocated (pattern, loc) ->
        let pattern, annotation = clean_pattern loc pattern in
        PLocated (pattern, loc), annotation

    | PAny ->
        PAny, TyUnknown
  in
  clean_pattern dummy_loc pattern
;;


let rec translate_pattern env = function
  | PVar x ->
      E.PVar (x, location env)
  | PTuple ps ->
      E.PTuple (List.map (translate_pattern env) ps)
  | PConstruct (datacon, fieldpats) ->
      (* Performs a side-effect! *)
      let resolved_datacon = resolve_datacon env datacon in
      let fields, pats = List.split fieldpats in
      let pats = List.map (translate_pattern env) pats in
      E.PConstruct (resolved_datacon, List.combine fields pats)
  | PLocated (p, pos) ->
      translate_pattern (locate env pos) p
  | PAs (p, x) ->
      (* The internal syntax allows a pattern on the right-hand side,
        because this is more regular, even the surface syntax does
        not allow it. *)
      E.PAs (translate_pattern env p, translate_pattern env (PVar x))
  | PConstraint _ ->
        Log.error "[clean_pattern] should've been called on that type before!"
  | PAny ->
      E.PAny
;;


(* -------------------------------------------------------------------------- *)

(* Expressions *)

let strip_tapp = function
  | Ordered t ->
      t
  | Named (_, t) ->
      t
;;

let map_tapp f = function
  | Ordered t ->
      E.Ordered (f t)
  | Named (x, t) ->
      E.Named (x, f t)
;;

let rec translate_expr (env: env) (expr: expression): E.expression =
  match expr with
  | EConstraint (e, t) ->
      let e = translate_expr env e in
      let t = translate_type_reset_no_kind env t in
      E.EConstraint (e, t)

  | EVar x ->
      evar (find_variable env x)

  | EBuiltin b ->
      E.EBuiltin b

  | ELet (flag, patexprs, body) ->
      let env, patexprs = translate_patexprs env flag patexprs in
      let body = translate_expr env body in
      E.ELet (flag, patexprs, body)

  | EFun (vars, arg, return_type, body) ->

      (* Introduce all universal bindings. *)
      let env = extend env vars in
      let vars = List.map (fun binding -> name_user env binding, UserIntroduced) vars in

      (* Interpret the argument type as a pattern. *)
      let p = type_to_pattern arg in

      (* Translate the function type. *)
      let universal_bindings, arg, return_type =
        translate_arrow_type env arg return_type
      in

      (* Introduce all other bindings in scope: these will end up in the
       * EBigLambdas, so they must be introduced before translating the function
       * body. *)
      let env = extend env universal_bindings in

      (* Introduce a fresh name for the argument. *)
      let x = fresh_var "/arg" in
      let env = extend env [ x, KTerm, location env ] in
      (* Introduce "let p = x in ..." in front of the body. This is subtle: by
         doing so, we capture the references to [bv p] within [body], so that
         these names now refer to this [let] definition, instead of referring
         to the [Lambda]-bound names in [universal_bindings]. It should work? *)
      let body = ELet (Nonrecursive, [ p, EVar (Unqualified x) ], body) in

      (* Now translate the body. *)
      let body = translate_expr env body in

      (* Build a little lambda. *)
      let body = E.ELambda (arg, return_type, body) in

      (* All universal bindings returned by [translate_arrow_type] are
       * auto-introduced universal bindings at kind [term]. *)
      let universal_bindings = List.map (fun binding -> name_auto binding, AutoIntroduced) universal_bindings in

      (* Build big Lambdas. *)
      E.EBigLambdas (vars @ universal_bindings, body)

  | EAssign (e1, f, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      (* Careful not to copy [f], so as to preserve sharing! *)
      E.EAssign (e1, f, e2)

  | EAssignTag (e1, datacon, info) ->
      let resolved_datacon = resolve_datacon env datacon in
      let e1 = translate_expr env e1 in
      (* Careful not to copy [x], so as to preserve sharing! *)
      E.EAssignTag (e1, resolved_datacon, info)

  | EAccess (e, f) ->
      let e = translate_expr env e in
      (* Careful not to copy [f], so as to preserve sharing! *)
      E.EAccess (e, f)

  | EAssert t ->
      let t, _, _ = translate_type env t in
      E.EConstraint (E.e_unit, T.TyBar (Types.ty_unit, t))

  | EApply (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EApply (e1, e2)

  | ETApply (e1, ts) ->
      let e1 = translate_expr env e1 in
      let ts = List.map (fun t ->
        map_tapp (translate_type_reset_no_kind env) t,
        KindCheck.infer_reset env (strip_tapp t)
      ) ts in
      List.fold_left (fun e (t, k) -> E.ETApply (e, t, k)) e1 ts

  | EMatch (b, e, patexprs) ->
      let e = translate_expr env e in
      let patexprs = List.map (fun (pat, expr) ->
        (* Extract assertions from the pattern. *)
        let pat, annotation = clean_pattern pat in
        (* If there is an annotation, and there's no top-level enclosing PAs
         * already, we need to add one! *)
        let pat, name =
          if annotation = TyUnknown then
            pat, None
          else
            match pat with
            | PLocated (PAs (_, x), _) ->
                pat, Some x
            | _ ->
                let name = fresh_var "/a" in
                PAs (pat, name), Some name
        in
        (* Translate the pattern. *)
        let sub_env = extend env (bv pat) in
        let pat = translate_pattern env pat in
        (* Bind the names for further translating, and don't forget to include
         * assertions in the translation as well. *)
        let expr =
          if annotation <> TyUnknown then
            translate_expr sub_env (
              ESequence (
                EAssert (
                  TyAnchoredPermission (
                    TyVar (Unqualified (Option.extract name)),
                    annotation
                  )
                ),
                expr
              )
            )
          else
            translate_expr sub_env expr
        in
        pat, expr) patexprs
      in
      E.EMatch (b, e, patexprs)

  | ETuple expressions ->
      E.ETuple (List.map (translate_expr env) expressions)

  | EConstruct (datacon, fieldexprs) ->
      (* Performs a side-effect! *)
      let resolved_datacon = resolve_datacon env datacon in
      let fieldexprs = List.map (fun (field, expr) ->
        field, translate_expr env expr) fieldexprs
      in
      E.EConstruct (resolved_datacon, fieldexprs)

  | EIfThenElse (b, e1, e2, e3) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      let e3 = translate_expr env e3 in
      E.EIfThenElse (b, e1, e2, e3)

  | EWhile (t, e1, e2) ->
      (* New name for the loop function. *)
      let name = fresh_var "/loop" in
      (* [call] is: loop() *)
      let call = EApply (EVar (Unqualified name) , ETuple []) in
      (* [body] is: if e₁ then begin e₂ ; loop() end *)
      let body = EIfThenElse (false, e1, ESequence (e2, call), ETuple []) in
      (* [f] is: fun (|t) : () -> [body] *)
      let f = EFun ([], TyBar(TyTuple[], t), TyTuple [], body) in
      (* The actual translation: let rec loop = [f] in loop() *)
      translate_expr env
        (ELet (Recursive, [(PVar name, f)] , call))

  | EFor (t, (x, _, _), e1, f, e2, e) ->
      let name = fresh_var "/loop" in
      let name_e2 = fresh_var "/max" in
      (* [vi] is: x *)
      let vi = EVar (Unqualified x) in
      let mkop s = EVar (Unqualified (Variable.register s)) in
      (* [next_op] is: + or - *)
      (* [cmp_op] is: <= or >= or < or > *)
      let next_op, cmp_op = match f with
      | To -> mkop "+", mkop "<="
      | Downto -> mkop "-", mkop ">="
      | Below -> mkop "+", mkop "<"
      | Above -> mkop "-", mkop ">"
      in
      (* [next] is: [vi] [next_op] 1 *)
      let next = EApply (
        next_op,
        ETuple [vi; EInt 1]
      ) in
      (* [call e] is: loop ([e]) *)
      let call e = EApply (EVar (Unqualified name), e) in
      (* [cmp] is: [vi] [cmp_op] max *)
      let cmp = EApply (cmp_op, ETuple [vi; EVar (Unqualified name_e2)]) in
      (* [body] is: if [cmp] then begin e; [call next] end *)
      let body = EIfThenElse (
        false, cmp, ESequence (e, call next), ETuple []
      ) in
      let ty_int = TyVar (Unqualified (Variable.register "int")) in
      (* [f] is: fun (x: int|t) : () -> [body] *)
      let f = EFun ([], TyBar(TyNameIntro (x, ty_int), t), TyTuple [], body) in 
      (* The actual translation is:
       * let max = eh in 
       * let rec loop = [f] in loop(el) *)
      translate_expr env (
        ELet (Nonrecursive, [(PVar name_e2, e2)],
          ELet (Recursive, [(PVar name, f)], call e1)
        )
      )

  | ESequence (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.(ELet (Nonrecursive, [p_unit, e1], e2))

  | ELocated (e, p) ->
      let e = translate_expr env e in
      E.ELocated (e, p)

  | EInt i ->
      E.EInt i

  | EExplained e ->
      let e = translate_expr env e in
      E.EExplained e

  | EGive (x, e) ->
      E.EGive (translate_expr env x, translate_expr env e)

  | ETake (x, e) ->
      E.ETake (translate_expr env x, translate_expr env e)

  | EOwns (x, e) ->
      E.EOwns (translate_expr env x, translate_expr env e)

  | EFail ->
      E.EFail

(* This function desugars a list of [pattern * expression] and returns the
 * desugared version. The expressions may have been annotated with type
 * constraints, according to the type annotations present in the pattern. *)
and translate_patexprs
      (env: env)
      (flag: rec_flag)
      (pat_exprs: (pattern * expression) list): env * E.patexpr list
    =
  let patterns, expressions = List.split pat_exprs in
  (* Remove all inner type annotations and transform them into a bigger type
   * constraint.*)
  let patterns, annotations = MzList.split_map clean_pattern patterns in
  (* Bind all the names in the sub-environment. *)
  let sub_env = extend env (bv (PTuple patterns)) in
  (* Translate the patterns. *)
  let patterns = List.map (translate_pattern env) patterns in
  (* Translate the expressions and annotations. *)
  let expressions, annotations = match flag with
    | Recursive ->
        List.map (translate_expr sub_env) expressions,
        List.map (translate_type_reset_no_kind sub_env) annotations
    | Nonrecursive ->
        List.map (translate_expr env) expressions,
        List.map (translate_type_reset_no_kind env) annotations
  in
  (* Turn them into constrainted expressions if need be. *)
  let expressions = List.map2 (fun expr annot ->
      if annot <> T.TyUnknown then
        E.EConstraint (expr, annot)
      else
        expr
    ) expressions annotations
  in
  sub_env, List.combine patterns expressions
;;



let translate_item env item =
  match item with
  | DataTypeGroup data_type_group ->
      (* This just desugars the data type definitions, no binder is opened yet! *)
      let env, defs =
        (* Be strict if we're in an interface. *)
        translate_data_type_group extend env data_type_group
      in
      env, Some (E.DataTypeGroup defs)
  | ValueDefinitions (loc, flag, pat_exprs) ->
      (* Same here, we're only performing desugaring, we're not opening any
       * binders. *)
      let env = locate env loc in
      let env, pat_exprs = translate_patexprs env flag pat_exprs in
      let item = E.ValueDefinitions (loc, flag, pat_exprs) in
      env, Some item
  | ValueDeclaration ((x, _, _) as binding, ty) ->
      let ty = translate_type_reset_no_kind env ty in
      let env = extend env [ binding ] in
      env, Some (E.ValueDeclaration (x, ty))
  | OpenDirective mname ->
      dissolve env mname, None
;;

let rec translate_items env = function
  | item :: items ->
      let env, item = translate_item env item in
      let items = translate_items env items in
      Option.to_list item @ items
  | [] ->
      []
;;

(* [translate_implementation implementation] returns an
 * [Expressions.implementation], i.e. a desugared version of the entire
 * program. *)
let translate_implementation (env: env) (program: toplevel_item list): E.implementation =
  translate_items env program

(* [translate_interface] is used by the Driver, before importing an interface
 * into scope. *)
let translate_interface (env: env) (program: toplevel_item list): E.interface =
  translate_items env program

let translate_type_reset = translate_type_reset_no_kind
