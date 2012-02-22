(** Dealing with permissions: adding them to an environment, taking some out of
 * an environemnt, etc. *)

open Types

let raw_add (env: env) (point: PersistentUnionFind.point) (t: typ): env =
  match FactInference.analyze_type env t with
  | Duplicable _ ->
      replace_expr env point (fun binder -> { binder with duplicable = t :: binder.duplicable })
  | _ ->
      replace_expr env point (fun binder -> { binder with exclusive = t :: binder.exclusive })
;;
