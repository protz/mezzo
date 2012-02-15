(** Dealing with permissions: adding them to an environment, taking some out of
 * an environemnt, etc. *)

open Types

(* This function assumes that [t] is relevant when see from [index]. *)
let raw_add (env: env) (index: index) (t: typ): env =
  let _name, { point; _ } = find_expr env index in
  let is_duplicable =
    let k = index + 1 in
    let type_for_current_env = lift k t in
    match FactInference.analyze_type env type_for_current_env with
    | Duplicable _ ->
        true
    | _ ->
        false
  in
  let state =
    PersistentUnionFind.update (fun permissions ->
      if is_duplicable then
        { permissions with duplicable = t :: permissions.duplicable }
      else
        { permissions with exclusive = t :: permissions.exclusive }
    ) point env.state
  in
  { env with state }
;;
