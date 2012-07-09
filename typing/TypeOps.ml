(** A module for performing various transformations on types. *)

open Types
open Permissions
open Expressions

let strip_forall t =
  let rec strip acc = function
  | TyForall (b, t) ->
      strip (b :: acc) t
  | _ as t ->
      List.rev acc, t
  in
  strip [] t
;;

let add_forall bindings t =
  List.fold_right (fun binding t -> TyForall (binding, t)) bindings t
;;
 
(* This function tries to find all function types of the form

   ∀(x::TERM, y::TERM). (τ | x = y) -> τ'

   and transform them into

   ∀(x::TERM) τ -> τ'
*)
let cleanup_function_type env t body =

  let rec find (env: env) (t: typ) (e: expression option): typ * expression option =
    match t with
    | TyForall _ ->
        let vars, t = strip_forall t in
        let env, { points; subst_type; subst_expr; _ } = bind_vars env vars in
        let vars = List.combine vars points in
        let t = subst_type t in
        let e = Option.map subst_expr e in
        begin match t with
        | TyArrow _ ->
            cleanup env vars t e
        | _ ->
            let t, _ = find env t e in
            List.fold_right (fun ((x, k), p) t ->
              TyForall ((x, k), Flexible.tpsubst env (TyVar 0) p t)
            ) vars t, None
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

  (* [vars] have been opened in [t] and [e]. *)
  and cleanup (env: env) (vars: (type_binding * point) list) (t: typ) (e: expression option)
      : typ * expression option =
    match t with
    | TyArrow (t1, t2) ->
        (* Get all permissions in [t1]. *)
        let t1, perms = collect t1 in
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

        (* Now keep [t1] without these useless permissions! *)
        let t1 =
          if List.length perms > 0 then TyBar (t1, fold_star perms) else t1
        in

        (* Perform some light cleanup on [t2] too. *)
        let t2 =
          let t2, perms = collect t2 in
          let perms = List.flatten (List.map flatten_star perms) in
          let t2, _ = find env t2 None in
          let perms = List.map (fun t -> fst (find env t None)) perms in
          let perms = List.filter (function
            | TyAnchoredPermission (TyPoint p, TySingleton (TyPoint p')) ->
                not (same env p p')
            | _ ->
                true
          ) perms in
          if List.length perms > 0 then TyBar (t2, fold_star perms) else t2
        in

        let t = TyArrow (t1, t2) in

        (* Now put back the quantifiers into place, skipping those that have
         * been put back already. *)
        let env = refresh_mark env in
        let _env, t, e, _i = List.fold_right (fun ((_, k), p) (env, t, e, i) ->
          if is_marked env p then
            env, t, e, i
          else
            let env = mark env p in
            let name =
              let names = get_names env p in
              try List.find (fun x -> (Variable.print x).[0] <> '/') names
              with Not_found -> List.hd names
            in
            let t = Flexible.tpsubst env (TyVar 0) p t in
            (* The substitution functions won't traverse the binder we just
             * added, because there no [EBigLambda], so we need to take into
             * account the fact that we've traversed so many binders. *)
            let e = Option.map (epsubst env (EVar i) p) e in
            let e = Option.map (tepsubst env (TyVar i) p) e in
            env, TyForall ((name, k), t), e, i + 1
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
  let t = add_forall bindings t in
  let t, body = cleanup_function_type env t body in
  let bindings, t = strip_forall t in
  let arg, return_type = match t with TyArrow (t1, t2) -> t1, t2 | _ -> assert false in
  bindings, arg, return_type, body
;;
