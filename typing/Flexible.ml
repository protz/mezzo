(** This module is dedicated to the handling of flexible variables. *)

open Types

(* [has_flexible env t] checks [t] for flexible variables. *)
let has_flexible env t =
  let rec has_flexible t =
    match t with
    | TyUnknown
    | TyDynamic
    | TyVar _ ->
        false

    | TyPoint p ->
        if is_flexible env p then
          true
        else
          begin match structure env p with
          | Some t ->
              has_flexible t
          | None ->
              false
          end

    | TyForall (_, t)
    | TyExists (_, t) ->
        has_flexible t

    | TyBar (t1, t2)
    | TyArrow (t1, t2)
    | TyApp (t1, t2) ->
        has_flexible t1 || has_flexible t2

    | TyTuple components ->
        List.exists has_flexible components

    | TyConcreteUnfolded (_, fields) ->
        let fields = List.map (function
          | FieldValue (_, t)
          | FieldPermission t ->
              has_flexible t
        ) fields in
        List.exists (fun x -> x) fields

    | TySingleton t ->
        has_flexible t

    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        has_flexible t1 || has_flexible t2

    | TyEmpty ->
        false

    | TyConstraints (constraints, t) ->
        List.exists (fun (_, t) -> has_flexible t) constraints ||
        has_flexible t

  in
  has_flexible t
;;


(* [find_flexible env t] returns the list of points found in [t] that represent
 * flexible variables. *)
let find_flexible env t =
  let rec find_flexible t =
    match t with
    | TyUnknown
    | TyDynamic
    | TyVar _ ->
        []

    | TyPoint p ->
        if is_flexible env p then
          [p]
        else
          begin match structure env p with
          | Some t ->
              find_flexible t
          | None ->
              []
          end

    | TyForall (_, t)
    | TyExists (_, t) ->
        find_flexible t

    | TyBar (t1, t2)
    | TyArrow (t1, t2)
    | TyApp (t1, t2) ->
        find_flexible t1 @ find_flexible t2

    | TyTuple components ->
        List.flatten (List.map find_flexible components)

    | TyConcreteUnfolded (_, fields) ->
        let fields = List.map (function
          | FieldValue (_, t)
          | FieldPermission t ->
              find_flexible t
        ) fields in
        List.flatten fields

    | TySingleton t ->
        find_flexible t

    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        find_flexible t1 @ find_flexible t2

    | TyEmpty ->
        []

    | TyConstraints (constraints, t) ->
        find_flexible t @
        Hml_List.map_flatten (fun (_, t) -> find_flexible t) constraints
  in
  let points = find_flexible t in
  let rec strip_duplicates acc = function
    | p :: ps ->
        if List.length (List.filter (same env p) ps) > 0 then
          strip_duplicates acc ps
        else
          strip_duplicates (p :: acc) ps
    | [] ->
        acc
  in
  strip_duplicates [] points
;;


(* Substitute [t2] for [p] in [t1]. We allow [t2] to have free variables. *)
let tpsubst env (t2: typ) (p: point) (t1: typ) =
  let lift1 = lift 1 in
  let rec tsubst t2 t1 =
    match t1 with
      (* Special type constants. *)
    | TyUnknown
    | TyDynamic
    | TyVar _ ->
        t1

    | TyPoint p' ->
        if same env p p' then
          t2
        else
          t1

    | TyForall (binder, t) ->
        TyForall (binder, tsubst (lift1 t2) t)

    | TyExists (binder, t) ->
        TyExists (binder, tsubst (lift1 t2) t)

    | TyApp (t, t') ->
        TyApp (tsubst t2 t, tsubst t2 t')

    | TyTuple ts ->
        TyTuple (List.map (tsubst t2) ts)

    | TyConcreteUnfolded (name, fields) ->
       TyConcreteUnfolded (name, List.map (function
         | FieldValue (field_name, t) -> FieldValue (field_name, tsubst t2 t)
         | FieldPermission t -> FieldPermission (tsubst t2 t)) fields)

    | TySingleton t ->
        TySingleton (tsubst t2 t)

    | TyArrow (t, t') ->
        TyArrow (tsubst t2 t, tsubst t2 t')

    | TyAnchoredPermission (p, q) ->
        TyAnchoredPermission (tsubst t2 p, tsubst t2 q)

    | TyEmpty ->
        t1

    | TyStar (p, q) ->
        TyStar (tsubst t2 p, tsubst t2 q)

    | TyBar (t, p) ->
        TyBar (tsubst t2 t, tsubst t2 p)

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (f, t) -> f, tsubst t2 t) constraints in
        TyConstraints (constraints, tsubst t2 t)
  in
  tsubst t2 t1
;;


(* [generalize_flexible env t] takes all flexible variables in [t] and
 * generalizes them. *)
let generalize env t =
  let flexible = find_flexible env t in
  List.fold_right (fun p t ->
    let x = Variable.register (Utils.fresh_name "g") in
    let k = get_kind env p in
    TyForall (((Auto x, k, env.location), CanInstantiate), tpsubst env (TyVar 0) p t)
  ) flexible t
;;
