open TypeCore

(* -------------------------------------------------------------------------- *)

(* For pretty-printing. *)

exception NotFoldable

(** [fold_var env var] tries to find (hopefully) one "main" type for [var], by
    folding back its "main" type [t] into a form that's suitable for one
    thing, and one thing only: printing. *)
let rec fold_var (env: env) (depth: int) (var: var): (env * typ) option =
  if is_flexible env var || depth > 5 then raise NotFoldable;

  let perms = get_permissions env var in
  let perms = List.filter
    (function
      | TySingleton (TyOpen p) when same env p var ->
          false
      | TyUnknown ->
          false
      | _ ->
          true
    ) perms
  in
  match perms with
  | [] ->
      Some (env, TyUnknown)
  | t :: []
  | TyDynamic :: t :: []
  | t :: TyDynamic :: [] ->
      begin try
        let env, t = fold_type env (depth + 1) t in
        let env = set_permissions env var [TyDynamic] in
        Some (env, t)
      with NotFoldable ->
        None
      end
  | _ ->
      None


and fold_type (env: env) (depth: int) (t: typ): env * typ =
  if depth > 5 then
    raise NotFoldable;

  match t with
  | TyUnknown
  | TyDynamic ->
      env, t

  | TyBound _ ->
      Log.error "All types should've been opened at that stage"

  | TyOpen _ ->
      env, t

  | TyQ _
  | TyApp _ ->
      env, t

  | TySingleton (TyOpen p) ->
      begin match fold_var env (depth + 1) p with
      | Some t ->
          t
      | None ->
          raise NotFoldable
      end

  | TyTuple components ->
      let env, components =
        List.fold_left (fun (env, cs) t ->
          let env, t = fold_type env (depth + 1) t in
          env, t :: cs
        ) (env, []) components
      in
      let components = List.rev components in
      env, TyTuple components

  | TyAnd (c, t) ->
      let env, t = fold_type env (depth + 1) t in
      env, TyAnd (c, t)

  | TyConcrete branch ->
      let env, branch = fold_branch env (depth + 1) branch in
      env, TyConcrete branch

  | TySingleton _ ->
      env, t

  | TyArrow _ ->
      env, t

  | TyBar (t, p) ->
      let env, t = fold_type env (depth + 1) t in
      env, TyBar (t, p)

  | TyAnchoredPermission (x, t) ->
      let env, t = fold_type env (depth + 1) t in
      env, TyAnchoredPermission (x, t)

  | TyEmpty ->
      env, t

  | TyStar _ ->
      Log.error "Huh I don't think we should have that here"

and fold_branch env depth branch =
  let env, fields =
    List.fold_left (fun (env, fields) (n, t) ->
      let env, t = fold_type env depth t in
      env, (n, t) :: fields
    ) (env, []) branch.branch_fields in
  let branch_fields = List.rev fields in
  let env, branch_adopts = fold_type env depth branch.branch_adopts in
  let branch = { branch with
    branch_fields;
    branch_adopts;
  } in
  env, branch
;;

let fold_type env t =
  try
    let _, t = fold_type env 0 t in
    Some t
  with NotFoldable ->
    None
;;

let fold_var env t =
  Option.map snd (fold_var env 0 t)
;;


