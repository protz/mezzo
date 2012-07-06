(** A module for performing various transformations on types. *)

open Types
open Permissions

let rec flatten_star = function
  | TyStar (p, q) ->
      flatten_star p @ flatten_star q
  | TyEmpty ->
      []
  | TyAnchoredPermission _ as p ->
      [p]
  | _ ->
      Log.error "[flatten_star] only works for types with kind PERM"
;;

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
let cleanup_function_type env t =

  let bind_forall env t =
    let rec bind acc env = function
      | TyForall (binding, t) ->
          let env, t, p = bind_var_in_type2 env binding t in
          bind ((binding, p) :: acc) env t
      | _ as t ->
          env, List.rev acc, t
    in
    bind [] env t
  in

  let rec find env t =
    match t with
    | TyForall _ ->
        let env, vars, t = bind_forall env t in
        begin match t with
        | TyArrow _ ->
            let t = cleanup env vars t in
            t
        | _ ->
            let t = find env t in
            List.fold_right (fun ((x, k), p) t ->
              TyForall ((x, k), Flexible.tpsubst env (TyVar 0) p t)
            ) vars t
        end

    | TyUnknown
    | TyDynamic ->
        t

    | TyVar _
    | TyPoint _ ->
        t

    | TyExists _ ->
        t

    | TyApp _ ->
        t

    | TyTuple ts ->
        TyTuple (List.map (find env) ts)

    | TyConcreteUnfolded (datacon, fields) ->
        let fields = List.map (fun field ->
          match field with
          | FieldValue (name, t) ->
              FieldValue (name, find env t)
          | _ ->
              field
        ) fields in
        TyConcreteUnfolded (datacon, fields)

    | TySingleton _ ->
        t

    | TyArrow (t1, t2) ->
        TyArrow (find env t1, find env t2)

    | TyBar _ ->
        Log.error "[find] expects a type that has been run through [collect] before"

    | TyAnchoredPermission (x, t) ->
        TyAnchoredPermission (x, find env t)

    | TyEmpty ->
        t

    | TyStar (p, q) ->
        TyStar (find env p, find env q)

  and cleanup env vars = function
    | TyArrow (t1, t2) ->
        (* Get all permissions in [t1]. *)
        let t1, perms = collect t1 in
        let perms = List.flatten (List.map flatten_star perms) in

        (* Recursively clean up [t1], and the permissions too. *)
        let t1 = find env t1 in
        let perms = List.map (find env) perms in

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
          let t2 = find env t2 in
          let perms = List.map (find env) perms in
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
        let _env, t = List.fold_right (fun ((_, k), p) (env, t) ->
          if is_marked env p then
            env, t
          else
            let env = mark env p in
            let name =
              let names = get_names env p in
              try List.find (fun x -> (Variable.print x).[0] <> '/') names
              with Not_found -> List.hd names
            in
            env, TyForall ((name, k), Flexible.tpsubst env (TyVar 0) p t)
        ) vars (env, t) in
        
        t

    | _ ->
        Log.error "[cleanup_function_type] only accepts TyArrow"

  in

  find env t
;;

let simplify_function_def env bindings arg return_type =
  let t = TyArrow (arg, return_type) in
  let t = add_forall bindings t in
  let t = cleanup_function_type env t in
  let bindings, t = strip_forall t in
  let arg, return_type = match t with TyArrow (t1, t2) -> t1, t2 | _ -> assert false in
  bindings, arg, return_type
;;
