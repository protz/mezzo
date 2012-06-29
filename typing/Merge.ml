open Types
open Utils

module PointMap = Hml_Map.Make(struct
  type t = PersistentUnionFind.point
  let compare = PersistentUnionFind.compare
end)

type job = point * point * point

type outcome = MergeWith of point | Proceed | Abort

let merge_envs (top: env) (left: env * point) (right: env * point): env * point =
  Log.debug ~level:1 "--------- START MERGE ----------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, top);

  (* We use a work list (a LIFO) to schedule points for merging. This implements
   * a depth-first traversal of the graph, which is indeed what we want (for the
   * moment). *)
  let pending_jobs: job list ref = ref [] in
  let pop r = let v = List.hd !r in r := List.tl !r; v in
  let push r v = r := v :: !r in

  (* One invariant is that if you push a job, the job's destination point has
   * been allocated in the destination environment already. *)
  let push_job = push pending_jobs in
  let pop_job () = pop pending_jobs in

  (* We also keep a list of [left_point, right_point, dest_point] triples that
   * have been processed already. *)
  let known_triples: job list ref = ref [] in
  let dump_known_triples left_env right_env dest_env =
    let open TypePrinter in
    List.iter (fun (left_point, right_point, dest_point) ->
      Log.debug "%a / %a / %a"
        pnames (get_names left_env left_point)
        pnames (get_names right_env right_point)
        pnames (get_names dest_env dest_point)) !known_triples;
      Log.debug "";
  in


  (* This oracle decides what to do with a given job. There are three outcomes:
    - we've already mapped the left and right points to a certain point in the
      destination environment: just merge the desired point with the one that's
      been mapped already → this strategy tries to preserve sharing;
    - the destination point appears in [known_triples] already: we've already
      merged this point, don't touch it anymore;
    - there's no such thing: perform the merge operation with the triple.

    We can map a point from [left_env] or [right_env] to several points in
    [dest_env] but for a given point in [dest_env], only ONE point from
    [left_env] (resp. [right_point]) points to it.
  *)
  let what_should_i_do
      (left_env, left_point)
      (right_env, right_point)
      (dest_env, dest_point): outcome
    =
    (* We're using these as keys so we better make sure we're using the real
     * descriptor. This is safe: there will be no more merging operations on
     * [left_env] and [right_env]. *)
    let left_point = PersistentUnionFind.repr left_point left_env.state in
    let right_point = PersistentUnionFind.repr right_point right_env.state in

    (* Try to find a sharing opportunity. *)
    let merge_candidates = List.filter
      (fun (left_point', right_point', _) ->
        same left_env left_point left_point' &&
        same right_env right_point right_point')
      !known_triples
    in
    Log.check (List.length merge_candidates <= 1)
      "The list of known triples is not consistent";

    match merge_candidates with
    | [_, _, dest_point'] ->
        (* We can share! *)
        Log.debug ~level:4 "[oracle] merge job %a → %a"
          TypePrinter.pnames (get_names dest_env dest_point)
          TypePrinter.pnames (get_names dest_env dest_point');
        MergeWith dest_point'

    | _ ->
        (* Try to see if we've processed this point already. *)
        let same_dest = List.filter (fun (_, _, dest_point') ->
          same dest_env dest_point dest_point') !known_triples
        in
        Log.check (List.length same_dest <= 1)
          "The list of known triples is not consistent";

        if List.length same_dest = 0 then begin
          (* Sanity check. *)
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

          (* Remember the triple. *)
          push known_triples (left_point, right_point, dest_point);

          Log.debug "[oracle] processing job %a / %a / %a."
            TypePrinter.pnames (get_names left_env left_point)
            TypePrinter.pnames (get_names right_env right_point)
            TypePrinter.pnames (get_names dest_env dest_point);
          Proceed

        end else begin
          Log.debug ~level:4 "[oracle] discarding job since %a has been visited already"
            TypePrinter.pnames (get_names dest_env dest_point);
          (* We've proceed this point already, don't process it again. *)
          Abort

        end
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
  let dest_env, dest_root = bind_term ~include_equals:false dest_env root_name false in
  push_job (left_root, right_root, dest_root);


  (* This function, assuming the [left_point, right_point, dest_point] triple is
   * legal, will do a cross-product of [merge_type], trying as it goes to match
   * permissions together and substract them from their environments. *)
  let rec merge_points
      ((left_env, left_point): env * point)
      ((right_env, right_point): env * point)
      ((dest_env, dest_point): env * point): env * env * env
    =

    Log.debug "[merge_points] %a / %a / %a."
      TypePrinter.pnames (get_names left_env left_point)
      TypePrinter.pnames (get_names right_env right_point)
      TypePrinter.pnames (get_names dest_env dest_point);

    match what_should_i_do (left_env, left_point) (right_env, right_point) (dest_env, dest_point) with
    | Abort ->
        (* Can't process the job, do nothing. *)
        left_env, right_env, dest_env

    | MergeWith dest_point' ->
        (* The oracle told us to merge. Do it. *)
        let dest_env = merge_left dest_env dest_point' dest_point in
        left_env, right_env, dest_env

    | Proceed ->

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
                if Option.is_some merge_result then begin
                  Log.debug ~level:4 "  → this merge between %a and %a was succesful"
                    Variable.p (get_name left_env left_point)
                    Variable.p (get_name right_env right_point);
                end;
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
                  let left_perms =
                    if FactInference.is_duplicable left_env left_perm then
                      left_perm :: left_perms
                    else
                      left_perms
                  in
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
        left_env, right_env, dest_env

  (* This is the core of the merge algorithm: this is where we compare a type
   * from the left with a type from the right and decide how to merge the two
   * together. *)
  and merge_type
      ((left_env, left_perm): env * typ)
      ((right_env, right_perm): env * typ)
      (dest_env: env): (env * typ) option
    =

    let bind_merge dest_env left_p right_p =
      let name = Variable.register (fresh_name "merge_point") in
      let dest_env, dest_p = bind_term ~include_equals:false dest_env name false in
      push_job (left_p, right_p, dest_p);
      Log.debug ~level:4
        "  [push_job] %a / %a / %a"
        TypePrinter.pnames (get_names left_env left_p)
        TypePrinter.pnames (get_names right_env right_p)
        TypePrinter.pnames (get_names dest_env dest_p);
      dest_env, dest_p
    in

    let () =
      let open TypePrinter in
      Log.debug ~level:4
        "  [merge_type] %a with %a"
        pdoc (ptype, (left_env, left_perm))
        pdoc (ptype, (right_env, right_perm));
    in

    match left_perm, right_perm with
    | TyPoint left_p, TyPoint right_p ->
        let dest_env, dest_p = bind_merge dest_env left_p right_p in
        Some (dest_env, TyPoint dest_p)

    | TySingleton left_t, TySingleton right_t ->
        Option.bind
          (merge_type (left_env, left_t) (right_env, right_t) dest_env)
          (fun (dest_env, dest_t) -> Some (dest_env, TySingleton dest_t))

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

  (* The main loop. *)
  let state = ref (left_env, right_env, dest_env) in
  while List.length !pending_jobs > 0 do
    (* Get the current merge state. *)
    let left_env, right_env, dest_env = !state in
    (* Next task: merge [left_point] and [right_point] into [dest_point]. *)
    let left_point, right_point, dest_point = pop_job () in
    (* Well, let's do it. *)
    let left_env, right_env, dest_env =
      merge_points
        (left_env, left_point)
        (right_env, right_point)
        (dest_env, dest_point)
    in
    (* And save it. *)
    state := (left_env, right_env, dest_env);
  done;

  (* Now we're just interested in [dest_env]. *)
  let _, _, dest_env = !state in

  Log.debug ~level:4 "------------ END MERGE ------------\n";
  dump_known_triples left_env right_env dest_env;

  (* So return it. *)
  dest_env, dest_root
;;
