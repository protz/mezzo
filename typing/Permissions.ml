(** This module provides permission manipulation functions. *)

open Types

(* [raw_add env p t] adds [t] to the list of permissions for [p]. *)
let raw_add (env: env) (point: point) (t: typ): env =
  match FactInference.analyze_type env t with
  | Duplicable _ ->
      replace_expr env point (fun binder -> { binder with duplicable = t :: binder.duplicable })
  | _ ->
      replace_expr env point (fun binder -> { binder with exclusive = t :: binder.exclusive })
;;

let fresh_name prefix =
  let counter = ref 0 in
  let n = string_of_int !counter in
  counter := !counter + 1;
  prefix ^ n
;;


(* [unfold env t] returns [env, t] where [t] has been unfolded, which
 * potentially led us into adding new points to [env]. *)
let rec unfold (env: env) ?(hint: string option) (t: typ): env * typ =

  (* This auxiliary function takes care of inserting an indirection if needed,
   * that is, a [=foo] type with [foo] being a newly-allocated [point]. *)
  let rec insert_point (env: env) (hint: string) (t: typ): env * typ =
    match t with
    | TySingleton _ ->
        env, t
    | _ ->
        (* The [expr_binder] also serves as the binder for the corresponding
         * TERM type variable. *)
        let env, p = bind_expr env (Variable.register hint) in
        (* This will take care of unfolding where necessary. *)
        let env = add_no_refresh env p t in
        env, TySingleton (TyPoint p)

  and unfold (env: env) ?(hint: string option) (t: typ): env * typ =
    let hint = Option.map_none (fresh_name "t_") hint in
    match t with
    | TyUnknown
    | TyDynamic
    | TyPoint _
    | TySingleton _
    | TyArrow _
    | TyEmpty ->
        env, t

    | TyVar _ ->
        Log.error "No unbound variables allowed here"

    (* TEMPORARY it's unclear what we should do w.r.t. quantifiers... *)
    | TyForall _
    | TyExists _ ->
        env, t

    | TyStar (p, q) ->
        let env, p = unfold env ~hint p in
        let env, q = unfold env ~hint q in
        env, TyStar (p, q)

    | TyAnchoredPermission (x, t) ->
        let env, t = unfold env ~hint t in
        env, TyAnchoredPermission (x, t)

    (* If this is the application of a data type that only has one branch, we
     * know how to unfold this. Otherwise, we don't! *)
    | TyApp _ ->
      begin
        let cons, args = flatten_tyapp t in
        match cons with
        | TyPoint p ->
          begin
            match branches_for_type env p with
            | Some [branch] ->
                if Mark.equals env.mark (get_mark env p) then
                  env, t
                else
                  let env = set_mark env p env.mark in
                  (* Reversing so that the i-th element in the list has De Bruijn
                   * index i in the data type def. *)
                  let args = List.rev args in
                  let branch = Hml_List.fold_lefti (fun i branch arg ->
                    subst_data_type_def_branch arg i branch) branch args
                  in
                  let t = TyConcreteUnfolded branch in
                  unfold env ~hint t
            | _ ->
              env, t
          end
        | _ ->
            Log.error "The head of a type application should be a type variable."
      end

    (* We're only interested in unfolding structural types. *)
    | TyTuple components ->
        let env, components = Hml_List.fold_lefti (fun i (env, components) -> function
          | TyTupleComponentPermission _ as component ->
              env, component :: components
          | TyTupleComponentValue component ->
              let hint = Printf.sprintf "%s_%d" hint i in
              let env, component = insert_point env hint component in
              env, TyTupleComponentValue component :: components
        ) (env, []) components in
        env, TyTuple (List.rev components)

    | TyConcreteUnfolded (datacon, fields) ->
        let env, fields = List.fold_left (fun (env, fields) -> function
          | FieldPermission _ as field ->
              env, field :: fields
          | FieldValue (name, field) ->
              let hint =
                Hml_String.bsprintf "%s_%a_%a" hint Datacon.p datacon Field.p name
              in
              let env, field = insert_point env hint field in
              env, FieldValue (name, field) :: fields
        ) (env, []) fields
        in
        env, TyConcreteUnfolded (datacon, List.rev fields)

  in
  unfold env ?hint t

and refine_type (env: env) (t1: typ) (t2: typ): typ option =
  assert false

and refine (env: env) (point: point) (t: typ): env =
  assert false

and add_no_refresh (env: env) (point: point) (t: typ): env =
  let hint = name_for_expr env point in
  let env, t = unfold env ?hint t in
  raw_add env point t
;;

(* [add env point t] adds [t] to the list of permissions for [p], performing all
 * the necessary legwork. *)
let add (env: env) (point: point) (t: typ): env =
  let env = refresh_mark env in
  add_no_refresh env point t
;;
