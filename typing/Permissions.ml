(** Dealing with permissions: adding them to an environment, taking some out of
 * an environemnt, etc. *)

open Env
open Types

let raw_add (program_env: program_env) (working_env: working_env)
    (level: level) (t: typ): working_env =
  (* We first need to determine whether the permission we're adding ends up
   * duplicable or not. *)
  (* TODO somehow reuse rev_duplicables from {!FactInference}. Will have to make
   * sure that function works on the most general type of environments, not just
   * its specific environment. *)
  let point = LevelMap.find level working_env.point_of_ident in
  let is_duplicable = false in
  let state = PersistentUnionFind.update (fun permissions ->
      if is_duplicable then
        { permissions with duplicable = t :: permissions.duplicable }
      else
        { permissions with exclusive = t :: permissions.exclusive }
    ) point working_env.state in
  { working_env with state }
;;
