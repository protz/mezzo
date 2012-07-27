open Types
open Utils

type job = point * point * point

type outcome = MergeWith of point | Proceed | Abort

let add_location dest_env dest_point right_location =
  replace dest_env dest_point (fun (head, binding) ->
    { head with locations = right_location :: head.locations }, binding
  )
;;

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
      let letter = Auto (Variable.register letter) in
      bind_type env letter env.location ~flexible:true Affine kind
    in
    env, point :: points) (left_env, []) arg_kinds letters
  in
  let t_app_left = fold_tyapp (TyPoint t_dest) (List.map (fun x -> TyPoint x) arg_points_l) in
  (* Chances are this will perform a merge in [left_env]: this is why
   * we're returning [left_env]. *)
  let left_env = Permissions.sub_type left_env left_perm t_app_left in
  left_env, t_app_left
;;


let merge_flexible_with_term_in_sub_env top right_env p p' =
  let works = valid top p' in
  if works then begin
    Log.check (is_term top p') "Malformed singleton type";
    Some (merge_left right_env p' p)
  end else begin
    None
  end
;;


let merge_envs (top: env) (left: env * point) (right: env * point): env * point =
  Log.debug ~level:3 "\n--------- START MERGE ----------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, top);

  Log.debug ~level:3 "\n------------ LEFT --------------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, fst left);

  Log.debug ~level:3 "\n------------ RIGHT -------------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, fst right);

  Log.debug ~level:3 "\n--------------------------------\n";

  (* We use a work list (a LIFO) to schedule points for merging. This implements
   * a depth-first traversal of the graph, which is indeed what we want (for the
   * moment). *)
  let pending_jobs: job list ref = ref [] in
  let pop r = let v = List.hd !r in r := List.tl !r; v in
  let push r v = r := v :: !r in
  let remove r v =
    match Hml_List.take (fun v' -> if v = v' then Some () else None) !r with
    | Some (remaining, _) ->
        r := remaining
    | None ->
        assert false
  in

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

  (* If one of our jobs is based on [left_point] and [right_point], we may have
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
              Lexer.p dest_env.location
              pvar name
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
  let root_name = Auto (Variable.register (fresh_name "merge_root")) in
  let dest_env, dest_root = bind_term ~include_equals:false dest_env root_name dest_env.location false in
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

    let left_env = locate left_env (List.hd (get_locations left_env left_point)) in
    let right_env = locate right_env (List.hd (get_locations right_env right_point)) in

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

              let works right_perm =
                merge_type (left_env, left_perm) (right_env, right_perm) dest_env
              in

              begin match Hml_List.take works right_perms with
              | Some (right_perms, (right_perm, (left_env, right_env, dest_env, dest_perm))) ->

                  Log.debug ~level:4 "  → this merge between %a and %a was succesful"
                    TypePrinter.pvar (get_name left_env left_point)
                    TypePrinter.pvar (get_name right_env right_point);

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

  (* end merge_points *)

  (* This is the core of the merge algorithm: this is where we compare a type
   * from the left with a type from the right and decide how to merge the two
   * together. *)
  and merge_type
      ((left_env, left_perm): env * typ)
      ((right_env, right_perm): env * typ)
      (dest_env: env): (env * env * env * typ) option
    =

    (* Allocate a new point [dest_p] in [dest_env] and schedule [left_p] and [right_p]
     * for merging with [dest_p]. Return [dest_env, dest_p]. *)
    let bind_merge dest_env left_p right_p =
      (* As a small optimization, if the point we're allocating is about to be
       * merged immediately by [merge_points], we don't allocate it at all
       * (which means less output, less fresh names, etc.). *)
      match merge_candidate (left_env, left_p) (right_env, right_p) with
      | Some dest_p ->
          dest_env, dest_p
      | None ->
          let name = Auto (Variable.register (fresh_name "merge_point")) in
          let dest_env, dest_p = bind_term ~include_equals:false dest_env name left_env.location false in
          let dest_env = add_location dest_env dest_p right_env.location in
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

    (* Because the order is important, we try various "strategies" that attempt
     * to solve this merge problem. A strategy just returns an option: if it
     * didn't work, we just try the next strategy. If all strategies fail, this
     * means we can't merge these two types together! Thankfully, [merge_points]
     * knows how to deal with that. *)
    let strategies = [

      (* Simple equals strategy. *)
      lazy begin
        try
          if equal top left_perm right_perm then begin
            Log.debug "→ fast_path, the types are equal in the original environment, \
              don't touch them";
            Some (left_env, right_env, dest_env, left_perm)
          end else begin
            None
          end
        with UnboundPoint ->
          None
      end;


      (* The flex-with-structure strategy, lefty version.
       *
       * This just steps through a flexible variable that has a structure. *)
      lazy begin
        match left_perm, right_perm with
        | TyPoint left_p, _ ->
            structure left_env left_p >>= fun left_perm ->
            merge_type (left_env, left_perm) (right_env, right_perm) dest_env
        | _ ->
            None
      end;

      (* The flex-with-structure strategy, righty version.
       *
       * And just for the record, this is *not* the same as putting both in the
       * same match statement!
       *)
      lazy begin
        match left_perm, right_perm with
        | _, TyPoint right_p ->
            structure right_env right_p >>= fun right_perm ->
            merge_type (left_env, left_perm) (right_env, right_perm) dest_env
        | _ ->
            None
      end;


      (* Point-to-point strategy.
       *
       * This covers the following cases. Greek letters are flexible variables.
       * - int vs int
       * - x vs y
       * - α vs int
       * - α vs β *)
      lazy begin
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

            | true, false ->
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

            | true, true ->
                let k = get_kind left_env left_p in
                Log.check (k = get_kind right_env right_p) "Kinds inconsistent!";

                begin match merge_candidate (left_env, left_p) (right_env, right_p) with
                | Some dest_p ->
                    Some (left_env, right_env, dest_env, TyPoint dest_p)
                | None ->
                    Log.check (k <> KTerm) "Remove this when we have a testcase, \
                      and try to understand what's happening, and if it's \
                      correct!";

                    let dest_env, dest_p =
                      bind_var dest_env ~flexible:true (get_name left_env left_p, k, dest_env.location)
                    in
                    push known_triples (left_p, right_p, dest_p);

                    Some (left_env, right_env, dest_env, TyPoint dest_p)
                end

            end
        | _ ->
            None
      end;


      (* Flexible type variable strategy.
       *
       * If we have a flexible variable on one side or another, just merge it
       * and we're done (as long as the other type makes sense in the
       * destination environment).
       *
       * This must come *after* the point-to-point strategy. *)
      lazy begin
        try_merge_flexible (left_env, left_perm) (right_env, right_perm) dest_env
      end;


      (* General strategy. *)
      lazy begin
        match left_perm, right_perm with
        | TySingleton left_t, TySingleton right_t ->
            let r = merge_type (left_env, left_t) (right_env, right_t) dest_env in
            r >>= fun (left_env, right_env, dest_env, dest_t) ->
            Some (left_env, right_env, dest_env, TySingleton dest_t)

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
              left_env >>= fun left_env ->
              right_env >>= fun right_env ->

              Log.debug ~level:3 "[cons_vs_cons] subtractions performed, got: %a vs %a"
                TypePrinter.ptype (left_env, t_app_left)
                TypePrinter.ptype (right_env, t_app_right);

              let r = merge_type (left_env, t_app_left) (right_env, t_app_right) dest_env in
              r >>= fun (left_env, right_env, dest_env, dest_perm) ->
              let dest_perm = Flexible.generalize dest_env dest_perm in
              Some (left_env, right_env, dest_env, dest_perm)

            else
              None


        | TyConcreteUnfolded (datacon_l, _), _ ->
            let t_left = type_for_datacon left_env datacon_l in
            let t_dest = PersistentUnionFind.repr t_left left_env.state in

            let left_env, t_app_left =
              build_flexible_type_application (left_env, left_perm) (dest_env, t_dest)
            in

            left_env >>= fun left_env ->
            merge_type (left_env, t_app_left) (right_env, right_perm) dest_env


        | _, TyConcreteUnfolded (datacon_r, _) ->
            let t_right = type_for_datacon right_env datacon_r in
            let t_dest = PersistentUnionFind.repr t_right right_env.state in

            let right_env, t_app_right =
              build_flexible_type_application (right_env, right_perm) (dest_env, t_dest)
            in

            right_env >>= fun right_env ->
            merge_type (left_env, left_perm) (right_env, t_app_right) dest_env


        | TyApp _, TyApp _ ->
            (* Sigh, we still don't flatten automatically type applications... *)
            let consl, argsl = flatten_tyapp left_perm in
            let consr, argsr = flatten_tyapp right_perm in

            (* Merge the constructors. This should be a no-op, unless they're
             * distinct, in which case we stop here. *)
            let r = merge_type (left_env, consl) (right_env, consr) dest_env in
            r >>= fun (left_env, right_env, dest_env, cons) ->

            (* So the constructors match. Let's now merge pairwise the arguments. *)
            let r = Hml_List.fold_left2i (fun i acc argl argr ->
              (* We keep the current triple of environments and the merge
               * arguments in the accumulator. *)
              acc >>= fun (left_env, right_env, dest_env, args) ->
              let v =
                (* Here, variance comes into play. The merge operation is a
                 * disjunction, so it "goes up" (subtyping-wise), that is, it is
                 * covariant. So if we need to recursively merge type parameters,
                 * we need to make sure the type is covariant for that parameter!
                 * If it's contravariant, we should do a conjunction (that is, the
                 * intersection) of types: this is the dual operation of the
                 * merge. I'm not going to write 1000 more lines just for that, so
                 * we're conservative, and move up the variance lattice, and
                 * consider the parameter to be invariant. *)
                match variance dest_env !!cons i with
                | Covariant ->
                    merge_type (left_env, argl) (right_env, argr) dest_env
                | _ ->
                    try_merge_flexible (left_env, argl) (right_env, argr) dest_env
              in
              v >>= fun (left_env, right_env, dest_env, arg) ->
              (* The parameter was merged. Return a valid accumulator. *)
              Some (left_env, right_env, dest_env, arg :: args)
            ) (Some (left_env, right_env, dest_env, [])) argsl argsr in
            r >>= fun (left_env, right_env, dest_env, args) ->

            (* Yay! All type parameters were merged. Reverse the list. *)
            let args = List.rev args in

            (* Re-fold the type application. *)
            let t = fold_tyapp cons args in

            (* And we're good to go. *)
            Some (left_env, right_env, dest_env, t)

        | TyForall (binding_left, t_l), TyForall (binding_right, t_r) ->
            (* This code-path is correct but frankly, we shouldn't have to
             * go there _at all_ yet. If two types are equal, then they must go
             * through the fast-path. Otherwise, this means that they contain TERM
             * variables that are local to a branch, and we don't know how to
             * handle that... *)

            (* First, check that the kinds are equal. *)
            let (_, k_l, left_location), (_, k_r, right_location) = binding_left, binding_right in
            if k_l = k_r then

              (* Bind the variables as rigid. *)
              let left_env, t_l, left_point = bind_var_in_type2 left_env binding_left t_l in
              let right_env, t_r, right_point = bind_var_in_type2 right_env binding_right t_r in

              (* Pick the name from the left... *)
              let binding = binding_left in
              let name, k, _ = binding in

              (* Bind the corresponding rigid variable in the destination
               * environment. Remember the triple. *)
              let dest_env, dest_point = bind_var dest_env (name, k, left_location) in
              let dest_env = add_location dest_env dest_point right_location in
              push known_triples (left_point, right_point, dest_point);

              (* Try to perform the merge. *)
              begin match merge_type (left_env, t_l) (right_env, t_r) dest_env with
              | Some (left_env, right_env, dest_env, t) ->
                  (* Yes? Re-generalize... *)
                  Some (
                    left_env, right_env, dest_env,
                    TyForall (binding, Flexible.tpsubst dest_env (TyVar 0) dest_point t)
                  )
              | None ->
                  (* Don't keep this triple since we're throwing away the
                   * environments. *)
                  remove known_triples (left_point, right_point, dest_point);
                  None
              end
            else
              None


        | _ ->
            None
      end;

    ] in

    Hml_List.find_opt Lazy.force strategies

  (* end merge_types *)

  (* I feel like this is the only place where we need to apply the singleton
   * subtyping rule (for the merge operation).
   *
   * Let us imagine that [t] is a singleton type [=x].
   * - If the try block succeeds,
   *   * [x] makes sense in both environments,
   *   * [p] is instantiated into [=x],
   *   * the flexible-structure strategy will call [merge_type] again with [=x]
   *     vs [=x]
   *   * this will merge into [=x].
   * - If the try block above does not succeed, [x] is local to this sub-environment.
   *   * we get the duplicable permissions of [p],
   *   * we try to merge [p] with one of them, preferably not the singleton one,
   *     since that one, again, doesn't make sense in a top-level environment.
   *)
  and try_merge_flexible (left_env, left_perm) (right_env, right_perm) dest_env =
    match left_perm, right_perm with
    (* We can instantiate a flexible variable, as long as the type on the other
     * side makes sense in the original environment. *)
    | TyPoint p, t when is_flexible left_env p ->
        begin try
          (* Will raise [UnboundPoint] if we can't get [t] to make sense in
             the toplevel environment. *)
          let t = clean top right_env t in
          let left_env = instantiate_flexible left_env p t in
          Some (left_env, right_env, dest_env, t)
        with UnboundPoint ->
          match t with
          | TySingleton (TyPoint p') ->
              Hml_List.find_opt
                (fun right_perm -> merge_type (left_env, left_perm) (right_env, right_perm) dest_env)
                (Permissions.dup_perms_no_singleton right_env p')
          | TyPoint _ ->
              Log.error "This should've been taken care of by the point-to-point \
                strategy";
          | _ ->
              None
        end

    | t, TyPoint p when is_flexible right_env p ->
        begin try
          let t = clean top left_env t in
          let right_env = instantiate_flexible right_env p t in
          Some (left_env, right_env, dest_env, t)
        with UnboundPoint ->
          match t with
          | TySingleton (TyPoint p') ->
              Hml_List.find_opt
                (fun left_perm -> merge_type (left_env, left_perm) (right_env, right_perm) dest_env)
                (Permissions.dup_perms_no_singleton left_env p')
          | TyPoint _ ->
              Log.error "This should've been taken care of by the point-to-point \
                strategy";
          | _ ->
              None
        end

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
  let left_env, right_env, dest_env = !state in

  if false then dump_known_triples left_env right_env dest_env;
  Log.debug ~level:3 "\n--------- END MERGE ----------\n\n%a"
    TypePrinter.pdoc (TypePrinter.print_permissions, dest_env);
  Log.debug ~level:3 "\n--------------------------------\n";

  (* So return it. *)
  dest_env, dest_root
;;
