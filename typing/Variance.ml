open Types

type t = variance

let lub a b =
  match a, b with
  | Invariant, _
  | _, Invariant ->
      Invariant
  | Bivariant, x
  | x, Bivariant ->
      x
  | x, y ->
      if x = y then
        x
      else
        Invariant
;;

let (~~) = function
  | Invariant -> Invariant
  | Covariant -> Contravariant
  | Contravariant -> Covariant
  | Bivariant -> Bivariant
;;

let dot a b =
  match a, b with
  | Invariant, _ ->
      Invariant
  | Covariant, b ->
      b
  | Contravariant, b ->
      ~~b
  | Bivariant, _ ->
      Bivariant
;;

let variance env var_for_ith valuation b t =
  let rec var = function
    | TyUnknown
    | TyDynamic
    | TyVar _
    | TyEmpty ->
        Bivariant

    | TyPoint a ->
        if same env a b then
          Covariant
        else
          Bivariant

    | TyForall (_, t)
    | TyExists (_, t) ->
        var t

    | TyApp _ as t ->
        let cons, args = flatten_tyapp t in
        let vs = List.mapi (fun i arg ->
          let a = var_for_ith !!cons i in
          dot (valuation a) (var arg)
        ) args in
        List.fold_left lub Bivariant vs

    | TyTuple ts ->
        let vs = List.map var ts in
        List.fold_left lub Bivariant vs

    | TyConcreteUnfolded (_, fields) ->
        let vs = List.map (function
          | FieldValue (_, t) ->
              var t
          | FieldPermission p ->
              var p
        ) fields in
        List.fold_left lub Bivariant vs

    | TySingleton t ->
        var t

    | TyArrow (t1, t2) ->
        lub ~~(var t1) (var t2)

    | TyBar (t1, t2)
    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        lub (var t1) (var t2)
  in
  var t
;;


module P = struct
  type property = t
  let bottom = Bivariant
  let equal = (=)
  let is_maximal = (=) Invariant
end

module M = struct
  type key = point
  type 'data t = 'data PointMap.t ref
  let create () = ref PointMap.empty
  let clear m = m := PointMap.empty
  let add k v m = m := (PointMap.add k v !m)
  let find k m = PointMap.find k !m
  let iter f m = PointMap.iter f !m
end

module Solver = Fix.Make(M)(P)

let analyze_data_types env =
  (* Keep the original env fresh, since we're going to throw away most of the
   * work below. *)
  let original_env = env in
  
  (* Create a sub-enviroment where points have been allocated for each one of
   * the data type parameters. We keep a list of instantiated branches with
   * their corresponding point. *)
  let env, store =
    fold_types original_env (fun (env, acc) point { kind; _ } { definition; _ } ->
      match definition with
      | None ->
          Log.error "Only data type definitions here"
      | Some (None, _) ->
          env, acc
      | Some (Some (_flag, branches), _) ->
          let env, points, instantiated_branches =
            bind_datacon_parameters env kind branches
          in
          env, (point, (points, instantiated_branches)) :: acc
    ) (original_env, [])
  in

  (* This function is needed inside [variance]. *)
  let var_for_ith cons i =
    let _, (vars, _) = List.find (fun (cons', _) -> same env cons cons') store in
    List.nth vars i
  in

  (* This computes the rhs for a given variable. *)
  let equations var =
    let _, (_, branches) = List.find (fun (_, (vars, _)) ->
      List.exists (same env var) vars
    ) store in
    (fun valuation ->
      let vs = List.map
        (variance env var_for_ith valuation var)
        (List.map (fun x -> TyConcreteUnfolded x) branches)
      in
      List.fold_left lub Bivariant vs
    )
  in

  (* Solve! *)
  let valuation = Solver.lfp equations in

  (* Update the data type definitions. *)
  let original_env = List.fold_left (fun env (cons, (vars, _)) ->
    let variance = List.map valuation vars in
    replace_type env cons (fun binding ->
      let definition =
        match binding.definition with
        | Some ((Some _) as branches, _) ->
            Some (branches, variance)
        | _ ->
            Log.error "Only data type definitions here"
      in
      { binding with definition }
    )
  ) original_env store in
  original_env
;;
