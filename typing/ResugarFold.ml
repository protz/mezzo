open TypeCore
open Types
open TypePrinter

(* -------------------------------------------------------------------------- *)

(* For pretty-printing. This module is probably incorrect in many, many ways. *)

let depth_exceeded depth = depth > 6

let default env = env, TyUnknown

(** [fold_var env var] tries to find (hopefully) one "main" type for [var], by
    folding back its "main" type [t] into a form that's suitable for one
    thing, and one thing only: printing. *)
let rec fold_var (env: env) (depth: int) (var: var): env * typ =
  if is_flexible env var then begin
    Log.debug ~level:5 "%a is flexible, bailing out of fold." pnames (env, get_names env var);
    default env
  end
  
  else if depth_exceeded depth then begin
    Log.debug ~level:5 "maximum depth exceeded, bailing out of fold";
    default env
  end

  else
    let perms = get_permissions env var in
    try
      let interesting =
        try
          List.find (function
            | TySingleton _ | TyUnknown | TyDynamic -> false
            | _ -> true
          ) perms
        with Not_found ->
          List.find (function
            | TySingleton _ | TyUnknown -> false
            | _ -> true
          ) perms
      in
      let env = set_permissions env var (List.filter ((!=) interesting) perms) in
      let env, t = fold_type env (depth + 1) interesting in
      env, t
    with
    | Not_found ->
        Log.debug ~level:5 "%a has no interesting permission, bailing out of fold." pnames (env, get_names env var);
        default env


and fold_type (env: env) (depth: int) (t: typ): env * typ =
  if depth_exceeded depth then begin
    Log.debug ~level:5 "maximum depth exceeded, bailing out of fold";
    default env
  end
  
  else match t with
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
      fold_var env (depth + 1) p

  | TySingleton _ ->
      assert false

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
  snd @@ fold_type env 0 t
;;

let fold_var env t =
  snd @@ fold_var env 0 t
;;


