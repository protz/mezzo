(** A module for performing various transformations on types. *)

open Types
open Expressions
open Monadic

module Merge = Merge.Make(MOption)
module Permissions = Permissions.Make(MOption)
 
(* This function tries to find all function types of the form

   ∀(x::TERM, y::TERM). (τ | x = y) -> τ'

   and transform them into

   ∀(x::TERM) τ -> τ'
*)
let cleanup_function_type env t body =

  (* It's a little bit tricky because in a function expression, we need to
   * update the body so that the references to the universally quantified
   * variables are correct: we're removing binders! Therefore, these functions
   * take an optional argument that is only used in a meaningful way for the
   * "toplevel" function type (the one whose universally quantified binders are
   * referenced by the function body). The argument is just discarded for
   * nested, first-class function types that appear in the outermost function
   * type. *)

  (* This function always returns [None] except when returning [cleanup env ...]. *)
  let rec find (env: env) (t: typ) (e: expression option): typ * expression option =
    match t with
    | TyForall _ ->
        let vars, t' = strip_forall t in
        begin match t' with
        | TyArrow _ ->
            cleanup env vars t' e
        | _ ->
            t, None
        end

    | TyUnknown
    | TyDynamic ->
        t, None

    | TyVar _
    | TyPoint _ ->
        t, None

    | TyExists _ ->
        t, None

    | TyApp _ ->
        t, None

    | TyTuple ts ->
        TyTuple (List.map (fun t -> fst (find env t e)) ts), None

    | TyConcreteUnfolded (datacon, fields) ->
        let fields = List.map (fun field ->
          match field with
          | FieldValue (name, t) ->
              let t, _ = find env t e in
              FieldValue (name, t)
          | _ ->
              field
        ) fields in
        TyConcreteUnfolded (datacon, fields), None

    | TySingleton _ ->
        t, None

    | TyArrow (t1, t2) ->
        TyArrow (fst (find env t1 e), fst (find env t2 e)), None

    | TyBar _ ->
        Log.error "[find] expects a type that has been run through [collect] before"

    | TyAnchoredPermission (x, t) ->
        TyAnchoredPermission (x, fst (find env t e)), None

    | TyEmpty ->
        t, None

    | TyStar (p, q) ->
        TyStar (fst (find env p e), fst (find env q e)), None

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (c, t) ->
          c, fst (find env t e)
        ) constraints in
        TyConstraints (constraints, fst (find env t e)), None

  (* [vars] have been opened in [t] and [e]. *)
  and cleanup (env: env) (vars: type_binding list) (t: typ) (e: expression option)
      : typ * expression option =

    (* Open the binders before working on the type. *)
    let env, { points; subst_type; subst_expr; _ } = bind_vars env vars in
    let vars = List.combine vars points in
    let t = subst_type t in
    let e = Option.map subst_expr e in

    match t with
    | TyArrow (t1, t2) ->
        (* Put aside the constraints since we can't really simplify these, and
         * if we try to, they end up being copied in the return type, which
         * doesn't make much sense. *)
        let constraints, t1 =
          match t1 with TyConstraints (cs, t1) -> cs, t1 | _ -> [], t1
        in

        (* Get all permissions in [t1]. *)
        let t1, perms = Permissions.collect t1 in
        let perms = List.flatten (List.map flatten_star perms) in

        (* Recursively clean up [t1], and the permissions too. *)
        let t1, _ = find env t1 None in
        let perms, _ = List.split (List.map (fun t -> find env t None) perms) in

        (* Is this one of the quantifiers just above us? *)
        let suitable p =
          List.exists (fun (_, p') -> same env p p') vars
        in

        (* For all x = y permissions, just perform the corresponding union-find
         * operation; other permissions are kept. *)
        let env, perms = List.fold_left (fun (env, perms) perm ->
          match perm with
          | TyAnchoredPermission (TyPoint p, TySingleton (TyPoint p')) ->
              if suitable p && suitable p' then
                let env = merge_left env p p' in
                (env, perms)
              else
                env, perm :: perms
          | _ ->
              env, perm :: perms
        ) (env, []) perms in
        let perms = List.rev perms in

        (* Now keep [t1] without these useless permissions! *)
        let t1 =
          if List.length perms > 0 then TyBar (t1, fold_star perms) else t1
        in

        (* TODO: make sure that there's no chance we're left with constraints
         * that refer to variables that [cleanup] decided to get rid of. *)
        let t1 =
          if List.length constraints > 0 then TyConstraints (constraints, t1) else t1
        in

        (* Perform some light cleanup on [t2] too. *)
        let t2 =
          let t1_perms = perms in
          let t2, perms = Permissions.collect t2 in
          (* Make sure we get a list of individual permissions. *)
          let perms = List.flatten (List.map flatten_star perms) in
          let t2, _ = find env t2 None in
          (* Recursively simplify these permissions. *)
          let perms = List.map (fun t -> fst (find env t None)) perms in
          (* If there are equalities, only keep the meaningful ones. *)
          let perms = List.filter (function
            | TyAnchoredPermission (TyPoint p, TySingleton (TyPoint p')) ->
                not (same env p p')
            | _ ->
                true
          ) perms in
          (* Final refinement: only keep those permissions that are either not
           * duplicable or not already taken as an argument by the function. The
           * caller will always be able to duplicate it. *)
          let perms = List.filter (fun p ->
            FactInference.is_duplicable env p ^=>
            not (List.exists (fun p' -> equal env p p') t1_perms)
          ) perms in
          if List.length perms > 0 then TyBar (t2, fold_star perms) else t2
        in

        let t = TyArrow (t1, t2) in

        (* Now put back the quantifiers into place, skipping those that have
         * been put back already. *)
        let env = refresh_mark env in
        let _env, t, e, _i = List.fold_right (fun ((_, k, pos), p) (env, t, e, i) ->
          if is_marked env p then
            env, t, e, i
          else
            let env = mark env p in
            let name =
              let names = get_names env p in
              try List.find (function User _ -> true | _ -> false) names
              with Not_found -> List.hd names
            in
            let t = Flexible.tpsubst env (TyVar 0) p t in
            (* The substitution functions won't traverse the binder we just
             * added, because there no [EBigLambda], so we need to take into
             * account the fact that we've traversed so many binders. *)
            let e = Option.map (epsubst env (EVar i) p) e in
            let e = Option.map (tepsubst env (TyVar i) p) e in
            env, TyForall ((name, k, pos), t), e, i + 1
        ) vars (env, t, e, 0) in
        
        t, e

    | _ ->
        Log.error "[cleanup_function_type] only accepts TyArrow"

  in

  let t, e = find env t (Some body) in
  t, Option.extract e
;;

let simplify_function_def env bindings arg return_type body =
  let t = TyArrow (arg, return_type) in
  let t = fold_forall bindings t in
  let t, body = cleanup_function_type env t body in
  let bindings, t = strip_forall t in
  let arg, return_type = match t with TyArrow (t1, t2) -> t1, t2 | _ -> assert false in
  bindings, arg, return_type, body
;;

let rec mark_reachable env = function
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar _ ->
      env

  | TyPoint p ->
      if is_marked env p then
        env
      else
        let env = mark env p in
        begin match structure env p with
        | Some t ->
            mark_reachable env t
        | None ->
            if is_term env p then
              let permissions = get_permissions env p in
              List.fold_left mark_reachable env permissions
            else
              env
        end

  | TyForall (_, t)
  | TyExists (_, t) ->
      mark_reachable env t

  | TyBar (t1, t2)
  | TyAnchoredPermission (t1, t2)
  | TyStar (t1, t2)
  | TyApp (t1, t2) ->
      List.fold_left mark_reachable env [t1; t2]

  | TyTuple ts ->
      List.fold_left mark_reachable env ts

  | TyConcreteUnfolded (_, fields) ->
      let ts = List.map (function
        | FieldValue (_, t) ->
            t
        | FieldPermission _ ->
            Log.error "[collect] wanted here"
      ) fields in
      List.fold_left mark_reachable env ts

  | TySingleton t ->
      mark_reachable env t

  | TyArrow _ ->
      env

  | TyConstraints (constraints, t) ->
      let env = List.fold_left (fun env (_, t) ->
        mark_reachable env t
      ) env constraints in
      mark_reachable env t
;;
