(** Dealing with permissions: adding them to an environment, taking some out of
 * an environemnt, etc. *)

open Types

let raw_add (env: env)
    (index: index) (t: typ): env =
  (* We first need to determine whether the permission we're adding ends up
   * duplicable or not. *)
  (* TODO somehow reuse rev_duplicables from {!FactInference}. Will have to make
   * sure that function works on the most general type of environments, not just
   * its specific environment. *)
  let { point; _ } = ByIndex.find index env.expr_bindings in
  let is_duplicable = false in
  let state = PersistentUnionFind.update (fun permissions ->
      if is_duplicable then
        { permissions with duplicable = t :: permissions.duplicable }
      else
        { permissions with exclusive = t :: permissions.exclusive }
    ) point env.state in
  { env with state }
;;
