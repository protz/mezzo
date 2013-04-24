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

let rec flatten_star p =
  match p with
  | TyStar (t1, t2) ->
      flatten_star t1 @ flatten_star t2
  | TyEmpty ->
      []
  | TyVar _
  | TyConsumes _
  | TyAnchoredPermission _
  | TyApp _ ->
      [p]
  | TyLocated (p, _) ->
      flatten_star p
  | _ as p ->
      Log.error "[flatten_star] only works for types with kind PERM (%a)"
        Utils.ptag p
;;

let fold_star perms =
  if List.length perms > 0 then
    MzList.reduce (fun acc x -> TyStar (acc, x)) perms
  else
    TyEmpty
;;


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
    | TyLocated (t, p) ->
        (* Keep the location information, may be useful later on. *)
        let env = locate env p in
        let t, acc = strip_consumes env t in
        TyLocated (t, p), acc

    | TyTuple ts ->
        let ts, accs = List.split (List.map (strip_consumes env) ts) in
        TyTuple ts, List.flatten accs

    | TyConcrete ((datacon, fields), clause) ->
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
        TyConcrete ((datacon, fields), clause), acc

    | TyNameIntro (x, t) ->
        let t, acc = strip_consumes env t in
        TyNameIntro (x, t), acc

    | TyAnd (c, t) ->
        let t, acc = strip_consumes env t in
        TyAnd (c, t), acc

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
          List.map (function TyConsumes p -> None, p, location env | _ -> assert false) consumed
        in
        let p = fold_star kept in
        (* Minimal cleanup. *)
        (if List.length kept > 0 then TyBar (t, p) else t),
        acc @ consumed

    | TyConsumes t ->
        let name = fresh_var "/c" in
        let c = TyVar (Unqualified name) in
        let perm = TyAnchoredPermission (c, t) in
       TySingleton c,
        [Some name, perm, location env]

    | TyUnknown
    | TyDynamic
    | TyVar _
    | TySingleton _
    (* These are opaque, no consumes annotations inside of these. *)
    | TyForall _
    | TyExists _
    | TyImply _
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
  let names, perms, locations = MzList.split3 name_perms in
  let bindings = MzList.map_some (function
    | Some x, loc ->
        Some (x, KTerm, loc)
    | None, _ ->
        None

  ) (List.combine names locations) in
  t, bindings, perms
;;

let rec translate_type (env: env) (t: typ): T.typ =
  match t with
  | TyLocated (t, p) ->
      translate_type (locate env p) t

  | TyTuple ts ->
      T.TyTuple (List.map (translate_type env) ts)

  | TyUnknown ->
      T.TyUnknown

  | TyDynamic ->
      T.TyDynamic

  | TyEmpty ->
      T.TyEmpty

  | TyVar x ->
      tvar (find_variable env x)

  | TyConcrete ((dref, fields), clause) ->
      T.TyConcrete {
       T.branch_flavor = ();
       T.branch_datacon = resolve_datacon env dref;
       T.branch_fields = translate_fields env fields;
       T.branch_adopts =
         match clause with
         | None    -> TypeCore.ty_bottom
         | Some ty -> translate_type env ty
      }

  | TySingleton t ->
      T.TySingleton (translate_type env t)

  | TyApp _ ->
      let t, ts = flatten_tyapp t in
      T.TyApp (translate_type env t, List.map (translate_type_with_names env) ts)

  | TyArrow (t1, t2) ->
      let universal_bindings, t1, t2 = translate_arrow_type env t1 t2 in
      let arrow = T.TyArrow (t1, t2) in
      Types.fold_forall universal_bindings arrow

  | TyForall ((x, k, loc), t) ->
      let env = bind_local env (x, k) in
      T.TyQ (T.Forall, name_user env (x, k, loc), UserIntroduced, translate_type_with_names env t)

  | TyExists ((x, k, loc), t) ->
      let env = bind_local env (x, k) in
      T.TyQ (T.Exists, name_user env (x, k, loc), UserIntroduced, translate_type_with_names env t)

  | TyAnchoredPermission (t1, t2) ->
      T.TyAnchoredPermission (translate_type env t1, translate_type env t2)
       (* TEMPORARY should be translate_type_with_names on the right-hand side,
          but that causes a large number of failures (why?). *)

  | TyStar (t1, t2) ->
      T.TyStar (translate_type env t1, translate_type env t2)

  | TyNameIntro (x, t) ->
      (* [x: t] translates into [(=x | x@t)] -- with [x] bound somewhere above
         us. *)
      let x = tvar (find_variable env (Unqualified x)) in
      T.TyBar (
        T.TySingleton x,
        T.TyAnchoredPermission (x, translate_type env t)
      )

  | TyConsumes _ ->
      (* These should've been removed by [strip_consumes]. *)
      illegal_consumes env

  | TyBar (t1, t2) ->
      T.TyBar (translate_type env t1, translate_type env t2)

  | TyAnd (c, t) ->
      T.TyAnd (translate_constraint env c, translate_type env t)

  | TyImply (c, ty) ->
      translate_implication env [c] ty

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

and conjunction cs ty =
  match cs with
  | [] ->
      ty
  | c :: cs ->
      conjunction cs (TyAnd (c, ty))

and translate_constraint env (m, t) =
  (* There was a check that [t] is [TyBound _], but I have removed it. *)
  m, translate_type env t

and translate_data_type_def_branch
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
      translate_type_with_names env t

and translate_fields env fields =
  List.map (function
    | FieldValue (name, t) ->
        T.FieldValue (name, translate_type_with_names env t)
    | FieldPermission t ->
        T.FieldPermission (translate_type env t)
  ) fields

and translate_arrow_type env t1 t2 =

  (* Collect nested constraints and put them in an outermost position to
   * simplify as much as possible the function type. *)
  (* TEMPORARY I do not understand why several tests fail if I remove
     the three lines of the [TyAnd] case below? *)
  let rec collect_constraints t =
    match t with
    | TyAnd (c, t) ->
        let cs', t = collect_constraints t in
        c :: cs', t
    | _ ->
        [], t
  in

  let constraints, t1 = collect_constraints t1 in

  (* Get the implicitly quantified variables in [t1]. These will be
     quantified as universal variables above the arrow type. *)
  let t1_bindings = names t1 in

  (* This is the procedure that removes the consumes annotations. It is
   * performed in the surface syntax. The first step consists in carving out
   * the [consumes] annotations, replacing them with [=c]. *)
  let t1, perm_bindings, perms = strip_consumes env t1 in

  (* Now we give a name to [t1] so that we can speak about the argument in
   * the returned type. Note: this variable name is not lexable, so no risk
   * of conflict. *)
  let root = fresh_var "/root" in
  let root_binding = root, KTerm, location env in
  let root_var = TyVar (Unqualified root) in

  (* We now turn the argument into (=root | root @ t1 ∗ c @ … ∗ …) with [t1]
   * now devoid of any consumes annotations. *)
  let fat_t1 = TyBar (
    TySingleton root_var,
    fold_star (TyAnchoredPermission (root_var, t1) :: perms)
  ) in

  (* So that we don't mess up, we use unique names in the surface syntax and
   * let the translation phase do the proper index computations. *)
  let universal_bindings = t1_bindings @ perm_bindings @ [root_binding] in
  let env = extend env universal_bindings in
  let fat_t1 =
    List.fold_left (fun t c -> TyAnd (c, t)) fat_t1 constraints
  in
  let fat_t1 = translate_type env fat_t1 in


  (* We need to return the original permission on [t1], minus the components
   * that were consumed: these have been carved out of [t1] by
   * [strip_consumes]. *)
  let t2 = TyBar (
    t2,
    TyAnchoredPermission (root_var, t1)
  ) in

  (* The return type can also bind variables with [x: t]. These are
   * existentially quantified. *)
  let t2 = translate_type_with_names env t2 in

  (* Finally, translate the universal bindings as well. *)
  let universal_bindings =
    List.map (name_user env) t1_bindings @
    List.map name_auto perm_bindings @
    List.map name_auto [root_binding]
  in
  let universal_bindings = List.map (fun x -> x, AutoIntroduced) universal_bindings in
  universal_bindings, fat_t1, t2

and translate_type_with_names (env: env) (t: typ): T.typ =
  let bindings = names t in
  let env = extend env bindings in
  let t = translate_type env t in
  let t = Types.fold_exists (List.map (fun binding -> name_user env binding, UserIntroduced) bindings) t in
  t

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
      let t = translate_type_with_names env t in
      T.({ data_name = name;
        data_location = loc;
        data_definition = Abbrev t;
        data_variance = variance;
        data_fact = fact;
        data_kind = kind
      })
;;


(* [translate_data_type_group bind env tenv data_type_group] returns [env, group] where:
  - the type definitions have been added with the corresponding levels in [env]
  - type definitions have been desugared into [group].
  The [bind] parameter is normally [KindCheck.bind], but [Interfaces] supplies
  a different function.
*)
let translate_data_type_group
    (bind: env -> type_binding -> env)
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
  let sub_env = List.fold_left bind env bindings in

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
        let patterns, annotations = List.split (List.map (clean_pattern loc) patterns) in
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
      let t = translate_type_with_names env t in
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

      (* Translate the function type. *)
      let universal_bindings, arg, return_type =
        translate_arrow_type env arg return_type
      in

      (* Introduce all other bindings in scope *)
      let env = List.fold_left (fun env -> function
        | ((T.Auto x, k, _), _) | ((T.User (_, x), k, _), _) -> bind_local env (x, k)
      ) env universal_bindings in

      (* Now translate the body (which will probably refer to these bound
       * names). *)
      let body = translate_expr env body in
      let vars = List.map (name_user env) vars in
      let vars = List.map (fun x -> x, UserIntroduced) vars in
      E.EFun (vars @ universal_bindings, arg, return_type, body)

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
      let t = translate_type env t in
      E.EConstraint (E.e_unit, T.TyBar (Types.ty_unit, t))

  | EApply (e1, e2) ->
      let e1 = translate_expr env e1 in
      let e2 = translate_expr env e2 in
      E.EApply (e1, e2)

  | ETApply (e1, ts) ->
      let e1 = translate_expr env e1 in
      let ts = List.map (fun t ->
        map_tapp (translate_type_with_names env) t, infer env (strip_tapp t)
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
      (* The actual translation: let loop = [f] in loop() *)
      translate_expr env
        (ELet (Recursive, [(PVar name, f)] , call))

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
  let patterns, annotations = List.split (List.map clean_pattern patterns) in
  (* Bind all the names in the sub-environment. *)
  let sub_env = extend env (bv (PTuple patterns)) in
  (* Translate the patterns. *)
  let patterns = List.map (translate_pattern env) patterns in
  (* Translate the expressions and annotations. *)
  let expressions, annotations = match flag with
    | Recursive ->
        List.map (translate_expr sub_env) expressions,
        List.map (translate_type_with_names sub_env) annotations
    | Nonrecursive ->
        List.map (translate_expr env) expressions,
        List.map (translate_type_with_names env) annotations
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
        translate_data_type_group bind_local_loc env data_type_group
      in
      env, Some (E.DataTypeGroup defs)
  | ValueDefinitions (loc, flag, pat_exprs) ->
      (* Same here, we're only performing desugaring, we're not opening any
       * binders. *)
      let env = locate env loc in
      let env, pat_exprs = translate_patexprs env flag pat_exprs in
      let item = E.ValueDefinitions (loc, flag, pat_exprs) in
      env, Some item
  | ValueDeclaration (x, t, loc) ->
      check env t KType;
      let t = translate_type_with_names env t in
      let env = bind_local_loc env (x, KTerm, loc) in
      env, Some (E.ValueDeclaration (x, t))
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
