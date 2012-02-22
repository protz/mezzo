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
  let rec insert_point (env: env) (hint: string) (t: typ): env * typ =
    (* The [expr_binder] also serves as the binder for the corresponding TERM
     * type variable. *)
    let env, p = bind_expr env (Variable.register hint) in
    (* This will take care of unfolding where necessary. *)
    let env = add env p t in
    env, TySingleton (TyPoint p)

  and unfold (env: env) ?(hint: string option) (t: typ): env * typ =
    let hint = Option.map_none (fresh_name "t_") hint in
    match t with
    | TyUnknown
    | TyDynamic
    | TyPoint _
    | TyForall _
    | TyExists _
    | TyApp _
    | TySingleton _
    | TyArrow _
    | TyAnchoredPermission _
    | TyEmpty
    | TyStar _ ->
        env, t

    | TyVar _ ->
        Log.error "No unbound variables allowed here"

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

(* [add env point t] adds [t] to the list of permissions for [p], performing all
 * the necessary legwork. *)
and add (env: env) (point: point) (t: typ): env =
  let hint = name_for_expr env point in
  let env, t = unfold env ?hint t in
  raw_add env point t
;;
