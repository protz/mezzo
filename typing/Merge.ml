open Types
open Utils

module PointMap = Hml_Map.Make(struct
  type t = PersistentUnionFind.point
  let compare = PersistentUnionFind.compare
end)

type job = point * point * point

type outcome = MergeWith of point | Proceed | Abort

(* The logic is the same on both sides, but I'm writing this with
 * the left-side in mind. *)
let build_flexible_type_application (left_env, left_perm) (dest_env, t_dest) =
  (* First, find the definition of the type so that we know how to
   * instanciate parameters. *)
  let return_kind, arg_kinds = flatten_kind (get_kind dest_env t_dest) in
  Log.check (return_kind = KType) "Not implemented";

  let letters = Hml_Pprint.name_gen (List.length arg_kinds) in

  let left_env, arg_points_l = List.fold_left2 (fun (env, points) kind letter ->
    let env, point =
      bind_type env (Variable.register letter) ~flexible:true Affine kind
    in
    env, point :: points) (left_env, []) arg_kinds letters
  in
  let t_app_left = List.fold_left
    (fun t arg -> TyApp (t, arg))
    (TyPoint t_dest)
    (List.map (fun x -> TyPoint x) arg_points_l)
  in
  (* Chances are this will perform a merge in [left_env]: this is why
   * we're returning [left_env]. *)
  let left_env = Permissions.sub_type left_env left_perm t_app_left in
  left_env, t_app_left
;;

let merge_envs (top: env) (left: env * point) (right: env * point): env * point =
  Log.debug ~level:3 "--------- START MERGE ----------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, top);

  Log.debug ~level:3 "\n------------ LEFT --------------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, fst left);

  Log.debug ~level:3 "\n------------ RIGHT -------------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, fst right);

  Log.debug ~level:3 "\n\n--------------------------------\n\n";

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
      Log.debug ~level:3 "%a / %a / %a"
        pnames (get_names left_env left_point)
        pnames (get_names right_env right_point)
        pnames (get_names dest_env dest_point)) !known_triples;
      Log.debug "";
  in

  (* If one of our job is based on [left_point] and [right_point], we may have
   * mapped these two to a point in the destination environment already. *)
  let merge_candidate (left_env, left_point) (right_env, right_point): point option =
    let merge_candidates = List.filter
      (fun (left_point', right_point', _) ->
        same left_env left_point left_point' &&
        same right_env right_point right_point')
      !known_triples
    in
    Log.check (List.length merge_candidates <= 1)
      "The list of known triples is not consistent";
    match merge_candidates with
    | [_, _, dest_point'] -> Some dest_point'
    | _ -> None
  in

  let is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p) =
    match merge_candidate (left_env, left_p) (right_env, right_p) with
    | Some dest_p' ->
        same dest_env dest_p dest_p'
    | None ->
        false
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
     * [left_env] and [right_env].
     *
     * XXX: I think that because [merge_candidates] uses [same], this is
     * overkill. *)
    let left_point = PersistentUnionFind.repr left_point left_env.state in
    let right_point = PersistentUnionFind.repr right_point right_env.state in

    match merge_candidate (left_env, left_point) (right_env, right_point) with
    | Some dest_point' ->
        (* We can share! *)
        Log.debug ~level:3 "[oracle] merge job %a → %a"
          TypePrinter.pnames (get_names dest_env dest_point)
          TypePrinter.pnames (get_names dest_env dest_point');
        MergeWith dest_point'

    | None ->
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

          Log.debug ~level:3 "[oracle] processing job %a / %a / %a."
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
  let root_name = Variable.register (fresh_name "/merge_root") in
  let dest_env, dest_root = bind_term ~include_equals:false dest_env root_name false in
  push_job (left_root, right_root, dest_root);

  (* All bound types are kept, so remember that we know how these are mapped. *)
  let type_triples = fold_types top (fun ps p _ _ -> (p, p, p) :: ps) [] in
  List.iter (push known_triples) type_triples;


  (* This function, assuming the [left_point, right_point, dest_point] triple is
   * legal, will do a cross-product of [merge_type], trying as it goes to match
   * permissions together and subtract them from their environments. *)
  let rec merge_points
      ((left_env, left_point): env * point)
      ((right_env, right_point): env * point)
      ((dest_env, dest_point): env * point): env * env * env
    =

    Log.debug ~level:3 "[merge_points] %a / %a / %a."
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
            (dest_env, dest_perms): env * (typ list) * env * (typ list) * env * (typ list) =
          (* [left_perms] and [right_perms] are the remaining permissions that
           * we need to match together. *)
          match remaining_left_perms, right_perms with
          | [], _
          | _, [] ->
              (* Return the permissions left for both the left and the right
               * environment. *)
              left_env, didnt_work_left_perms, right_env, right_perms, dest_env, dest_perms
          | left_perm :: left_perms, right_perms ->

              (* This function returns the first right permission we found that
               * works, the remaining ones, and the result of the merge
               * operation. *)
              let rec find_couple didnt_work_right_perms right_perms =
                match right_perms with
                | [] ->
                    None
                | right_perm :: right_perms ->
                    let result =
                      merge_type (left_env, left_perm) (right_env, right_perm) dest_env
                    in
                    match result with
                    | Some result ->
                        Some (right_perm, didnt_work_right_perms @ right_perms, result)
                    | None ->
                        find_couple (right_perm :: didnt_work_right_perms) right_perms
              in

              begin match find_couple [] right_perms with
              | Some (right_perm, right_perms, (left_env, right_env, dest_env, dest_perm)) ->

                  Log.debug ~level:4 "  → this merge between %a and %a was succesful"
                    Variable.p (get_name left_env left_point)
                    Variable.p (get_name right_env right_point);

                  let left_is_duplicable = FactInference.is_duplicable left_env left_perm in
                  let right_is_duplicable = FactInference.is_duplicable right_env right_perm in
                  let duplicable =
                    match left_is_duplicable, right_is_duplicable with
                    | true, true ->
                        true
                    | _ ->
                        false
                  in
                  if duplicable then
                    merge_lists
                      (left_env, left_perms, left_perm :: didnt_work_left_perms)
                      (right_env, right_perm :: right_perms)
                      (dest_env, dest_perm :: dest_perms)
                  else
                    merge_lists
                      (left_env, left_perms, didnt_work_left_perms)
                      (right_env, right_perms)
                      (dest_env, dest_perm :: dest_perms)
              | None ->
                  merge_lists
                    (left_env, left_perms, left_perm :: didnt_work_left_perms)
                    (right_env, right_perms)
                    (dest_env, dest_perms)
              end


        in

        let left_perms = get_permissions left_env left_point in
        let right_perms = get_permissions right_env right_point in
        let left_env, left_perms, right_env, right_perms, dest_env, dest_perms =
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
      (dest_env: env): (env * env * env * typ) option
    =

    let bind_merge dest_env left_p right_p =
      (* As a small optimization, if the point we're allocating is bound to be
       * merged immediately by [merge_points], we don't allocate it at all
       * (which means less output, less fresh names, etc.). *)
      match merge_candidate (left_env, left_p) (right_env, right_p) with
      | Some dest_p ->
          dest_env, dest_p
      | None ->
          let name = Variable.register (fresh_name "/merge_point") in
          let dest_env, dest_p = bind_term ~include_equals:false dest_env name false in
          push_job (left_p, right_p, dest_p);
          Log.debug ~level:4
            "  [push_job] %a / %a / %a"
            TypePrinter.pnames (get_names left_env left_p)
            TypePrinter.pnames (get_names right_env right_p)
            TypePrinter.pnames (get_names dest_env dest_p);
          dest_env, dest_p
    in

    let open TypePrinter in
    Log.debug ~level:4
      "  [merge_type] %a with %a"
      ptype (left_env, left_perm)
      ptype (right_env, right_perm);

    let simple_equals = try equal top left_perm right_perm with UnboundPoint -> false in

    if simple_equals then begin
      Log.debug "→ fast_path, the types are equal in the original environment, \
        don't touch them";
      Some (left_env, right_env, dest_env, left_perm)

    end else begin
      match left_perm, right_perm with
      | TyPoint left_p, TyPoint right_p ->
          Log.check (is_type left_env left_p && is_type right_env right_p
            || is_term left_env left_p && is_term right_env right_p)
            "Sanity check failed";

          begin match is_flexible left_env left_p, is_flexible right_env right_p with
          | false, false ->
              let dest_env, dest_p = bind_merge dest_env left_p right_p in
              Some (left_env, right_env, dest_env, TyPoint dest_p)

          | false, true ->
              begin match structure left_env left_p with
              | Some left_perm ->
                  merge_type (left_env, left_perm) (right_env, right_perm) dest_env
              | None ->
                  let dest_p = PersistentUnionFind.repr left_p left_env.state in

                  (* This must be a top-level type and [left_p] must be valid in the
                   * destination environment. *)
                  Log.check (is_type dest_env dest_p) "A flexible variable must refer \
                    to a type defined in the top-level scope, we don't know how to treat \
                    flexible variables with kind other than TYPE yet.";

                  let right_env = merge_left right_env dest_p right_p in
                  Log.check (is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p))
                    "All top-level types should be in known_triples by default";

                  Some (left_env, right_env, dest_env, TyPoint dest_p)
              end

          | true, false ->
              begin match structure right_env right_p with
              | Some right_perm ->
                  merge_type (left_env, left_perm) (right_env, right_perm) dest_env
              | None ->
                  let dest_p = PersistentUnionFind.repr right_p right_env.state in

                  (* This must be a top-level type and [right_p] must be valid in the
                   * destination environment. *)
                  Log.check (is_type dest_env dest_p) "A flexible variable must refer \
                    to a type defined in the top-level scope, we don't know how to treat \
                    flexible variables with kind other than TYPE yet.";

                  let left_env = merge_left left_env dest_p left_p in
                  Log.check (is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p))
                    "All top-level types should be in known_triples by default";

                  Some (left_env, right_env, dest_env, TyPoint dest_p)
              end

          | true, true ->
              let k = get_kind left_env left_p in
              Log.check (k = get_kind right_env right_p) "Kinds inconsistent!";

              begin match merge_candidate (left_env, left_p) (right_env, right_p) with
              | Some dest_p ->
                  Some (left_env, right_env, dest_env, TyPoint dest_p)
              | None ->
                  let dest_env, dest_p =
                    bind_type dest_env (get_name left_env left_p) ~flexible:true Affine k
                  in
                  push known_triples (left_p, right_p, dest_p);

                  Some (left_env, right_env, dest_env, TyPoint dest_p)
              end

          end


      | TySingleton left_t, TySingleton right_t ->
          Option.bind
            (merge_type (left_env, left_t) (right_env, right_t) dest_env)
            (fun (left_env, right_env, dest_env, dest_t) ->
              Some (left_env, right_env, dest_env, TySingleton dest_t))

      | TyConcreteUnfolded (datacon_l, fields_l), TyConcreteUnfolded (datacon_r, fields_r) ->
          let t_left: point = type_for_datacon left_env datacon_l in
          let t_right: point = type_for_datacon right_env datacon_r in

          if Datacon.equal datacon_l datacon_r then
            (* Same constructors: both are in expanded form so just schedule the
             * points in their fields for merging. *)
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
            Some (left_env, right_env, dest_env, TyConcreteUnfolded (datacon_l, List.rev dest_fields))

          else if same dest_env t_left t_right then
            (* Same nominal type (e.g. [Nil] vs [Cons]). The procedure here is a
             * little bit more complicated. We need to take the nominal type (e.g.
             * [list]), and apply it to [a] flexible on both sides, allocate [a]
             * in [dest_env] and add the relevant triples in [known_triples].
             * Then, perform [Nil - list a] and [Cons - list a]. Then recursively
             * merge the variables pairwise, and if it's still flexible,
             * generalize (or maybe not?).
             *)

            let t_dest = PersistentUnionFind.repr t_left left_env.state in

            let left_env, t_app_left =
              build_flexible_type_application (left_env, left_perm) (dest_env, t_dest)
            in
            let right_env, t_app_right =
              build_flexible_type_application (right_env, right_perm) (dest_env, t_dest)
            in

            (* Did the subtractions succeed? *)
            begin match left_env, right_env with
            | Some left_env, Some right_env ->
                Log.debug ~level:3 "[cons_vs_cons] subtractions performed, got: %a vs %a"
                  TypePrinter.ptype (left_env, t_app_left)
                  TypePrinter.ptype (right_env, t_app_right);

                Option.bind
                  (merge_type (left_env, t_app_left) (right_env, t_app_right) dest_env)
                  (fun (left_env, right_env, dest_env, dest_perm) ->
                    let dest_perm = Flexible.generalize dest_env dest_perm in
                    Some (left_env, right_env, dest_env, dest_perm)
                  )

            | _ ->
                None
            end

          else
            None


      | TyConcreteUnfolded (datacon_l, _), _ ->
          let t_left = type_for_datacon left_env datacon_l in
          let t_dest = PersistentUnionFind.repr t_left left_env.state in

          let left_env, t_app_left =
            build_flexible_type_application (left_env, left_perm) (dest_env, t_dest)
          in

          Option.bind left_env (fun left_env ->
            merge_type (left_env, t_app_left) (right_env, right_perm) dest_env
          )


      | _, TyConcreteUnfolded (datacon_r, _) ->
          let t_right = type_for_datacon right_env datacon_r in
          let t_dest = PersistentUnionFind.repr t_right right_env.state in

          let right_env, t_app_right =
            build_flexible_type_application (right_env, right_perm) (dest_env, t_dest)
          in

          Option.bind right_env (fun right_env ->
            merge_type (left_env, left_perm) (right_env, t_app_right) dest_env
          )


      | TyApp (tl1, tl2), TyApp (tr1, tr2) ->
          Option.bind (merge_type (left_env, tl1) (right_env, tr1) dest_env)
            (fun (left_env, right_env, dest_env, t1) ->
              Option.bind (merge_type (left_env, tl2) (right_env, tr2) dest_env)
                (fun (left_env, right_env, dest_env, t2) ->
                  Some (left_env, right_env, dest_env, TyApp (t1, t2))))

      | TyForall (binding_left, t_l), TyForall (binding_right, t_r) ->
          (* XXX I'm pretty sure this codepath is untested... *)
          (* First, check that the kinds are equal. *)
          let k_l, k_r = snd binding_left, snd binding_right in
          if k_l = k_r then
            (* Bind the variables as rigid. *)
            let left_env, t_l, left_point = bind_var_in_type2 left_env binding_left t_l in
            let right_env, t_r, right_point = bind_var_in_type2 right_env binding_right t_r in
            (* Pick the name from the left... *)
            let binding = binding_left in
            let name, k = binding in
            (* Bind the corresponding rigid variable in the destination
             * environment. Remember the triple. *)
            let dest_env, dest_point = bind_type dest_env name Affine k in
            push known_triples (left_point, right_point, dest_point);
            (* Try to perform the merge. *)
            Option.bind (merge_type (left_env, t_l) (right_env, t_r) dest_env)
              (fun (left_env, right_env, dest_env, t) ->
                (* Yes? Re-generalize... *)
                Some (
                  left_env, right_env, dest_env,
                  TyForall (binding, Flexible.tpsubst dest_env (TyVar 0) dest_point t)
                )
              )
          else
            None

      | _ ->
          None

  end in (* end merge_types *)

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
  let left_env, right_env, dest_env = !state in

  dump_known_triples left_env right_env dest_env;
  Log.debug ~level:3 "--------- END MERGE ----------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, dest_env);

  (* So return it. *)
  dest_env, dest_root
;;
