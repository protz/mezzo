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

(** A module for performing various transformations on types. *)

open Types
open Expressions

(** [collect t] recursively walks down a type with kind TYPE, extracts all
    the permissions that appear into it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    PERM, which represents all the permissions that were just extracted. *)
let collect (t: typ): typ * typ list =
  let rec collect (t: typ): typ * typ list =
    match t with
    | TyUnknown
    | TyDynamic

    | TyVar _
    | TyPoint _

    | TyForall _
    | TyExists _
    | TyApp _

    | TySingleton _

    | TyArrow _ ->
        t, []

    (* Interesting stuff happens for structural types only *)
    | TyBar (t, p) ->
        let t, t_perms = collect t in
        let p, p_perms = collect p in
        t, p :: t_perms @ p_perms

    | TyTuple ts ->
        let ts, permissions = List.split (List.map collect ts) in
        let permissions = List.flatten permissions in
        TyTuple ts, permissions

    | TyConcreteUnfolded (datacon, fields, clause) ->
        let permissions, values = List.partition
          (function FieldPermission _ -> true | FieldValue _ -> false)
          fields
        in
        let permissions = List.map (function
          | FieldPermission p -> p
          | _ -> assert false) permissions
        in
        let sub_permissions, values =
         List.fold_left (fun (collected_perms, reversed_values) ->
            function
              | FieldValue (name, value) ->
                  let value, permissions = collect value in
                  permissions :: collected_perms, (FieldValue (name, value)) :: reversed_values
              | _ ->
                  assert false)
            ([],[])
            values
        in
        TyConcreteUnfolded (datacon, List.rev values, clause), List.flatten (permissions :: sub_permissions)

    | TyAnchoredPermission (x, t) ->
        let t, t_perms = collect t in
        TyAnchoredPermission (x, t), t_perms

    | TyEmpty ->
        TyEmpty, []

    | TyStar (p, q) ->
        let p, p_perms = collect p in
        let q, q_perms = collect q in
        TyStar (p, q), p_perms @ q_perms

    | TyConstraints _ ->
        t, []
  in
  collect t
;;
 
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

    | TyConcreteUnfolded (datacon, fields, clause) ->
        let fields = List.map (fun field ->
          match field with
          | FieldValue (name, t) ->
              let t, _ = find env t e in
              FieldValue (name, t)
          | _ ->
              field
        ) fields in
        TyConcreteUnfolded (datacon, fields, clause), None

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
  and cleanup (env: env) (vars: (type_binding * flavor) list) (t: typ) (e: expression option)
      : typ * expression option =
      List.iter (fun binding ->
        let open TypePrinter in
        let open ExprPrinter in
        Log.debug "%a" pdoc (print_ebinder env, binding)
      ) vars;

    let vars, flavors = List.split vars in

    (* Open the binders before working on the type. *)
    let env, { points; subst_type; subst_expr; _ } = bind_evars env vars in
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
        let perms = List.rev perms in

        (* Now keep [t1] without these useless permissions! *)
        let t1 =
          if List.length perms > 0 then TyBar (t1, fold_star perms) else t1
        in

        (* TODO: make sure that there's no chance we're left with constraints
         * that refer to variables that [cleanup] will decide to get rid of.
         * 20121004: but we never remove variables, do we? We just merge the
         * redundant ones together... so in the worst case, since all variables
         * are opened at this stage, when we close them, we will just refer to
         * the merged variable... *)
        let t1 =
          if List.length constraints > 0 then TyConstraints (constraints, t1) else t1
        in

        (* Perform some light cleanup on [t2] too. *)
        let t2 =
          let t1_perms = perms in
          let t2, perms = collect t2 in
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
           * caller will always be able to duplicate it (η-expansion argument). *)
          let perms = List.filter (fun p ->
            FactInference.is_duplicable env p ^=>
            not (List.exists (fun p' -> equal env p p') t1_perms)
          ) perms in
          if List.length perms > 0 then TyBar (t2, fold_star perms) else t2
        in

        let t = TyArrow (t1, t2) in

        (* Now put back the quantifiers into place, skipping those that have
         * been put back already. This function is correct because (total
         * handwaving time): the binders are kept in order, so if we go
         * left-to-right, we first hit user-defined binders, which *remain*
         * user-defined, and then we hit automatically-inserted-by-desugaring
         * binders, which will remain as such. *)
        let env = refresh_mark env in
        let _env, vars = List.fold_left2 (fun (env, vars) ((_, k, pos), p) flavor ->
          if is_marked env p then
            env, vars
          else
            let env = mark env p in
            let name =
              let names = get_names env p in
              try List.find (function User _ -> true | _ -> false) names
              with Not_found -> List.hd names
            in
            env, (name, k, pos, flavor, p) :: vars
        ) (env, []) vars flavors in
        let vars = List.rev vars in
        let _env, t, e, _i = List.fold_right (fun (name, k, pos, flavor, p) (env, t, e, i) ->
          let t = Flexible.tpsubst env (TyVar 0) p t in
          (* The substitution functions won't traverse the binder we just
           * added, because there no [EBigLambda], so we need to take into
           * account the fact that we've traversed so many binders. *)
          let e = Option.map (epsubst env (EVar i) p) e in
          let e = Option.map (tepsubst env (TyVar i) p) e in
          env, TyForall (((name, k, pos), flavor), t), e, i + 1
        ) vars (env, t, e, 0) in

        t, e

    | _ ->
        Log.error "[cleanup_function_type] only accepts TyArrow"

  in

  find env t body
;;

let simplify_function_def env bindings arg return_type body =
  let t = TyArrow (arg, return_type) in
  let t = fold_forall bindings t in
  let t, body = cleanup_function_type env t (Some body) in
  let body = Option.extract body in
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
  | TyStar (t1, t2) ->
      List.fold_left mark_reachable env [t1; t2]

  | TyApp (t1, t2) ->
      List.fold_left mark_reachable env (t1 :: t2)

  | TyTuple ts ->
      List.fold_left mark_reachable env ts

  | TyConcreteUnfolded (_, fields, clause) ->
      let ts = List.map (function
        | FieldValue (_, t) ->
            t
        | FieldPermission _ ->
            Log.error "[collect] wanted here"
      ) fields in
      let ts = clause :: ts in
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
