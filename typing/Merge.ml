open Types
open Permissions


type subpoint = env * point
type ('a, 'b) pair = { mutable left: 'a; mutable right: 'b }

let merge_envs (left: subpoint) (right: subpoint) (top: env) (return: point): env =
  let dest = empty in
  let roots = keys top in
  (* If an element is in the worklist, it is mapped already. *)
  let worklist = ref [] in
  let anon = {
    left: point PointMap.t;
    right: point PointMap.t;
  } in
  let is_mapped point point' anon =
    (* check that point and point' are either both present and point to the same
     * point or both absent *)
    ...
  in
  let map_anon (left: subpoint) (right: subpoint) =
    ...
  in
  let merge_points (left: subpoint) (right: subpoint) (dest: subpoint): env * env * env =
    let left_env, left_point = left in
    let right_env, right_point = right in
    let dest_env, dest_point = dest in
    cross-product merge_type
  in
  let merge_type (left: subtype) (right: subtype) (dest: env): env * typ option =
    let left_env, left_typ = left in
    let right_env, right_typ = right in
    let dest_env, dest_typ = dest in
    match left_typ, right_typ with
    | TyConcreteUnfolded _, TyConcreteUnfolded _ ->
        let points = List.map2 (fun (left_field, left_point) (right_field, right_point) ->
          assert left_field = right_field
          match is_mapped left_point right_point anon with
          | Some dest_point ->
              ty_equals dest_point
          | None ->
              let dest_point = map_anon left right in
              add_to_worklist left_point right_point dest_point
        ) _ _

  in
  let state = ref (left_env, right_env, dest_env) in
  let pop r = let v = List.hd !r in r := List.tl !r in
  while List.length !worklist > 0 do
    let left_env, right_env, dest_env = !state in
    let root_point = pop worklist in
    let left_point = find anon.left root_point in
    let right_point = find anon.right root_point in
    let left_env, right_env, dest_env =
      merge_points (left_env, left_point) (right_env, right_point) (dest_env, dest_point)
    in
    state := (left_env, right_env, dest_env);
  done;
  let _, _, dest_env = !state in
  dest_env
;;
