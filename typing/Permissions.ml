(** Dealing with permissions: adding them to an environment, taking some out of
 * an environemnt, etc. *)

open Types

let raw_add (env: env) (index: index) (t: typ): env =
  let _name, { point; _ } = find_expr env index in
  let is_duplicable =
    match FactInference.analyze_type env t with
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
