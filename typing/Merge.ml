open Types
open Utils

module PointMap = Hml_Map.Make(struct
  type t = PersistentUnionFind.point
  let compare = PersistentUnionFind.compare
end)

type ('a, 'b) pair = { mutable left: 'a; mutable right: 'b }
type job = point * point * point
type mapping = (point PointMap.t, point PointMap.t) pair

let merge_envs (top: env) (left: env * point) (right: env * point): env * point =

  (* We use a work list (a LIFO) to schedule points for merging. *)
  let worklist: job list ref = ref [] in
  let pop r = let v = List.hd !r in r := List.tl !r; v in
  let push r v = r := v :: !r in
  let push_job = push worklist in
  let pop_job () = pop worklist in

  (* We use a mapping that injects the set of points from the [left] and [right]
   * environments into the set of points from the [dest] environment. Initially,
   * the mapping is the identity function over the set of roots, that is, the
   * points defined in [top]. *)
  let mapping: mapping = {
    left = PointMap.empty;
    right = PointMap.empty;
  } in

  (* When tackling a merge job between points [left_point] and [right_point],
    merging into [dest_point], the following situations arise (see my notebook
    on 2012/06/28):
    i. neither [left_point] or [right_point] are mapped: update the mapping with
      the point that has been allocated for them in the destination environment;
    ii. [left_point] and [right_point] are mapped already:
      a. they point to the expected point in the destination environment: this is
        great!
      b. they point to a different point [p']: merge [dest_point] with [p']
        (situation 2 in the notebook),
    iii. either one of them is not mapped, or the two are mapped and point to
      conflicting points in the destination environment: this means a different
      decision has been made, and we need to bail out. This will result in no
      permissions for the allocated point, and we just learnt that this merge
      situation is not principal (situation 1 in the notebook).
  *)
  let try_map
      (mapping: mapping)
      (left_point: point)
      (right_point: point)
      (dest_env, dest_point): (env * mapping) option
    =
    
    if List.length (get_permissions dest_env dest_point) <> 0 then begin
      let open TypePrinter in
      Log.debug ~level:4 "Here is the state of [dest_env]\n%a" pdoc (print_permissions, dest_env);
      let name, binder = find_term dest_env dest_point in
      Log.debug ~level:4
        "%a %a shouldn't have any permissions but it has %a"
        Lexer.p dest_env.position
        Variable.p name
        pdoc (print_permission_list, (dest_env, binder));
      Log.error "The destination point must have an empty list of permissions!"
    end;
    let left_mapping = PointMap.find_opt left_point mapping.left in
    let right_mapping = PointMap.find_opt right_point mapping.right in
    match left_mapping, right_mapping with
    | Some left_dest_point, Some right_dest_point ->
        if same dest_env left_dest_point right_dest_point then begin
          (* situation ii. *)
          if same dest_env left_dest_point dest_point then begin
            (* situation ii.a. *)
            Some (dest_env, mapping)
          end else begin
            (* situation ii.b.

              The assertion at the beginning of the function makes sure it's
              safe to drop the descriptor of [dest_point]. *)
            let dest_env = merge_left dest_env left_dest_point dest_point in
            Some (dest_env, mapping)
          end
        end else begin
          (* situation iii. *)
          None
        end
    | None, None ->
        (* situation i. *)
        Some (dest_env, {
          left = PointMap.add left_point dest_point mapping.left;
          right = PointMap.add right_point dest_point mapping.right;
        })
    | _ ->
        (* situation iii. *)
        None
  in

  (* This is the destination environment; it will evolve over time. Initially,
   * it is empty. As an optimization, we keep the points that were previously
   * defined so that the mapping is the identity for all the points from [top]. *)
  let dest_env = fold_terms top (fun dest_env point _head _binder ->
    replace_term dest_env point (fun binder ->
      { binder with permissions = [] }
    )) top
  in

  (* All the roots should be merged. *)
  let roots = fold_terms top (fun acc k _ _ -> k :: acc) [] in
  List.iter (fun p -> push_job (p, p, p)) roots;

  (* Create an additional root for the result of the match. Schedule it for
   * merging, at the front of the list (this implements our first heuristic). *)
  let left_env, left_root = left in
  let right_env, right_root = right in
  let root_name = Variable.register (fresh_name "merge_root") in
  let dest_env, dest_root = bind_term dest_env root_name false in
  let dest_env = replace_term dest_env dest_root (fun binder ->
      { binder with permissions = [] }
    )
  in
  push_job (left_root, right_root, dest_root);


  (* This is the core of the merge algorithm: this is where we compare a type
   * from the left with a type from the right and decide how to merge the two
   * together. *)
  let merge_type
      ((left_env, left_perm): env * typ)
      ((right_env, right_perm): env * typ)
      (dest_env: env): (env * typ) option
    =

    let bind_merge dest_env left_p right_p =
      let name = Variable.register (fresh_name "merge_point") in
      let dest_env, dest_p = bind_term dest_env name false in
      push_job (left_p, right_p, dest_p);
      dest_env, dest_p
    in

    let () =
      let open TypePrinter in
      Log.debug ~level:4
        "%a [merge_type] %a with %a"
        Lexer.p dest_env.position
        pdoc (ptype, (left_env, left_perm))
        pdoc (ptype, (right_env, right_perm));
    in

    match left_perm, right_perm with
    | TyPoint left_p, TyPoint right_p ->
        let dest_env, dest_p = bind_merge dest_env left_p right_p in
        Some (dest_env, TyPoint dest_p)

    | TyConcreteUnfolded (datacon_l, fields_l), TyConcreteUnfolded (datacon_r, fields_r) ->
        if Datacon.equal datacon_l datacon_r then
          let dest_env, dest_fields =
            List.fold_left2 (fun (dest_env, dest_fields) field_l field_r ->
              match field_l, field_r with
              | FieldValue (name_l, TySingleton (TyPoint left_p)),
                FieldValue (name_r, TySingleton (TyPoint right_p)) ->
                  Log.check (Field.equal name_l name_r) "Not in order?";
                  let dest_env, dest_p = bind_merge dest_env left_p right_p in
                  (dest_env, FieldValue (name_l, ty_equals dest_p) :: dest_fields)
              | _ ->
                  Log.error "All permissions should be in expanded form."
            ) (dest_env, []) fields_l fields_r
          in
          Some (dest_env, TyConcreteUnfolded (datacon_l, List.rev dest_fields))

        else
          None

    | _ ->
        None

  in

  (* This function, assuming the [left_point, right_point, dest_point] triple is
   * legal, will do a cross-product of [merge_type], trying as it goes to match
   * permissions together and substract them from their environments. *)
  let merge_points
      (mapping: mapping)
      ((left_env, left_point): env * point)
      ((right_env, right_point): env * point)
      ((dest_env, dest_point): env * point): mapping * env * env * env
    =
    match try_map mapping left_point right_point (dest_env, dest_point) with
    | None ->
        (* Can't perform the merge, do nothing. *)
        mapping, left_env, right_env, dest_env

    | Some (dest_env, mapping) ->
        (* This function will just take an initially empty [dest_perms] and try
          all combinations pairwise from [left_perms] and [right_perms] to build
          [dest_perms]. It will return the unused permissions. *)
        let rec merge_lists
            (left_env, remaining_left_perms, didnt_work_left_perms)
            (right_env, right_perms)
            (dest_env, dest_perms) =
          (* [left_perms] and [right_perms] are the remaining permissions that
           * we need to match together. *)
          match remaining_left_perms, right_perms with
          | [], _
          | _, [] ->
              (* Return the permissions left for both the left and the right
               * environment. *)
              didnt_work_left_perms, right_perms, dest_env, dest_perms
          | left_perm :: left_perms, right_perms ->
              (* Try to find an item in [right_perms] that can be merged with
               * [left_perm]. *)
              let attempts = List.map (fun right_perm ->
                let merge_result = 
                  merge_type
                    (left_env, left_perm)
                    (right_env, right_perm)
                    dest_env
                in
                if Option.is_some merge_result then
                  Log.debug ~level:4 "  → this merge was succesful";
                right_perm, merge_result) right_perms
              in
              let worked, didnt_work =
                List.partition (fun (_, x) -> Option.is_some x) attempts
              in
              match worked with
              | (_, hd) :: tl ->
                  (* We just keep the first item that worked. *)
                  let the_rest = List.map fst (tl @ didnt_work) in
                  let dest_env, dest_perm = Option.extract hd in
                  merge_lists
                    (left_env, left_perms, didnt_work_left_perms)
                    (right_env, the_rest)
                    (dest_env, dest_perm :: dest_perms)
              | [] ->
                  merge_lists 
                    (left_env, left_perms, left_perm :: didnt_work_left_perms)
                    (right_env, right_perms)
                    (dest_env, dest_perms)
        in

        let left_perms = get_permissions left_env left_point in
        let right_perms = get_permissions right_env right_point in
        let left_perms, right_perms, dest_env, dest_perms =
          merge_lists (left_env, left_perms, []) (right_env, right_perms) (dest_env, [])
        in

        let left_env =
          replace_term left_env left_point (fun b -> { b with permissions = left_perms })
        in
        let right_env =
          replace_term right_env right_point (fun b -> { b with permissions = right_perms })
        in
        let dest_env =
          replace_term dest_env dest_point (fun b -> { b with permissions = dest_perms })
        in
        mapping, left_env, right_env, dest_env
  in


  (* The main loop. *)
  let state = ref (mapping, left_env, right_env, dest_env) in
  while List.length !worklist > 0 do
    (* Get the current merge state. *)
    let mapping, left_env, right_env, dest_env = !state in
    (* Next task: merge [left_point] and [right_point] into [dest_point]. *)
    let left_point, right_point, dest_point = pop_job () in
    (* Well, let's do it. *)
    let mapping, left_env, right_env, dest_env =
      merge_points
        mapping
        (left_env, left_point)
        (right_env, right_point)
        (dest_env, dest_point)
    in
    (* And save it. *)
    state := (mapping, left_env, right_env, dest_env);
  done;
  (* Now we're just interested in [dest_env]. *)
  let _, _, _, dest_env = !state in
  (* So return it. *)
  dest_env, dest_root
;;
