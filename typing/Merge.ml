(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

open Types

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
  let left_env, arg_points_l = make_datacon_letters left_env (get_kind dest_env t_dest) true (fun _ -> Affine) in
  let t_app_left = ty_app (TyPoint t_dest) (List.map (fun x -> TyPoint x) arg_points_l) in
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

let is_valid top sub t =
  try
    ignore (clean top sub t);
    true
  with UnboundPoint ->
    false
;;



module Lifo = struct
  type t = job list ref
  let create () = ref [];;
  let pop r = let v = List.hd !r in r := List.tl !r; v;;
  let push r v = r := v :: !r;;
  let remove r v =
    match Hml_List.take (fun v' -> if v = v' then Some () else None) !r with
    | Some (remaining, _) ->
        r := remaining
    | None ->
        assert false
  ;;
end

let actually_merge_envs (top: env) ?(annot: typ option) (left: env * point) (right: env * point): env * point =
  (* We use a work list (a LIFO) to schedule points for merging. This implements
   * a depth-first traversal of the graph, which is indeed what we want (for the
   * moment). *)
  let pending_jobs = Lifo.create () in

  (* One invariant is that if you push a job, the job's destination point has
   * been allocated in the destination environment already. *)
  let push_job = Lifo.push pending_jobs in
  let pop_job () = Lifo.pop pending_jobs in

  (* We also keep a list of [left_point, right_point, dest_point] triples that
   * have been processed already. *)
  let known_triples = Lifo.create () in
  let remember_triple = Lifo.push known_triples in
  let _forget_triple = Lifo.remove known_triples in
  let dump_known_triples left_env right_env dest_env =
    let open TypePrinter in
    List.iter (fun (left_point, right_point, dest_point) ->
      Log.debug ~level:3 "%a / %a / %a"
        pnames (left_env, get_names left_env left_point)
        pnames (right_env, get_names right_env right_point)
        pnames (dest_env, get_names dest_env dest_point)) !known_triples;
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

    match merge_candidate (left_env, left_point) (right_env, right_point) with
    | Some dest_point' ->
        (* We can share! *)
        Log.debug ~level:3 "[oracle] merge job %a → %a"
          TypePrinter.pnames (dest_env, get_names dest_env dest_point)
          TypePrinter.pnames (dest_env, get_names dest_env dest_point');
        MergeWith dest_point'

    | None ->
        (* Try to see if we've processed this point already. *)
        let same_dest = List.filter (fun (_, _, dest_point') ->
          same dest_env dest_point dest_point') !known_triples
        in
        Log.check (List.length same_dest <= 1) "The list of known triples is not consistent";

        (* Because [merge_candidates] returned [None], we know that we're not in
         * a case of sharing. So if one of the two checks below succeeds, this
         * means that we've visited either the left point with a different path
         * on the right side, or the converse. If the point is marked (and
         * [make_base_envs] marked those points that originally contained a
         * non-duplicable permission), then we're in a case of exclusive
         * resource allocation conflict: we're trying to use, say, the same
         * left_point for a different right_point. *)
        if List.exists (fun (l, _, _) ->
          same left_env left_point l && is_marked left_env l
        ) !known_triples then begin
          let open TypeErrors in
          let error = ResourceAllocationConflict left_point in
          if !Options.pedantic then
            raise_error left_env error
          else
            Log.warn "%a" print_error (left_env, error)
        end;
        if List.exists (fun (_, r, _) ->
          same right_env right_point r && is_marked right_env r
        ) !known_triples then begin
          let open TypeErrors in
          let error = ResourceAllocationConflict right_point in
          if !Options.pedantic then
            TypeErrors.raise_error right_env error
          else
            Log.warn "%a" print_error (right_env, error)
        end;


        if List.length same_dest = 0 then begin
          (* Remember the triple. *)
          remember_triple (left_point, right_point, dest_point);

          Log.debug ~level:3 "[oracle] processing job %a / %a / %a."
            TypePrinter.pnames (left_env, get_names left_env left_point)
            TypePrinter.pnames (right_env, get_names right_env right_point)
            TypePrinter.pnames (dest_env, get_names dest_env dest_point);
          Proceed

        end else begin
          Log.debug ~level:4 "[oracle] discarding job since %a has been visited already"
            TypePrinter.pnames (dest_env, get_names dest_env dest_point);

          (* This piece of code is actually dead because we always allocate a
           * fresh (existentially-quantified) point in the destination
           * environment. This means always call this function with [dest_point]
           * fresh, which means there's no way we processed it already. *)
          if true then assert false;

          (* Do nothing, since it would be illegal! *)
          Abort

        end
  in


  let dump_envs left_env right_env dest_env =

    Log.debug ~level:3 "\n------------ LEFT --------------\n\n%a"
      TypePrinter.pdoc (TypePrinter.print_permissions, left_env);

    Log.debug ~level:3 "\n------------ RIGHT -------------\n\n%a"
      TypePrinter.pdoc (TypePrinter.print_permissions, right_env);

    Log.debug ~level:3 "\n------------ DEST -------------\n\n%a"
      TypePrinter.pdoc (TypePrinter.print_permissions, dest_env);

    Log.debug ~level:3 "\n--------------------------------\n";

  in


  let make_base_envs ?annot () =

    Log.debug ~level:3 "\n--------- START MERGE @ %a ----------\n\n%a\n\n"
      Lexer.p top.location
      TypePrinter.pdoc (TypePrinter.print_permissions, top);

    (* This is the destination environment; it will evolve over time. Initially,
     * it is empty. As an optimization, we keep the points that were previously
     * defined so that the mapping is the identity for all the points from [top]. *)
    let dest_env = fold_terms top (fun dest_env point _head _binder ->
      replace_term dest_env point (fun binder ->
        { binder with permissions = initial_permissions_for_point point }
      )) top
    in

    (* TODO we should iterate over all pairs of roots here, and see if they've
     * been merged in both sub-environments. In that case, they should be merged
     * beforehand in the destination environment too. Merges in local
     * sub-environments can happen because a dynamic == test refined the
     * permissions. *)

    (* All the roots should be merged. *)
    let roots = fold_terms top (fun acc k _ _ -> k :: acc) [] in
    List.iter (fun p -> push_job (p, p, p)) roots;

    (* Create an additional root for the result of the match. Schedule it for
     * merging, at the front of the list (this implements our first heuristic). *)
    let left_env, left_root = left in
    let right_env, right_root = right in
    let root_name = fresh_auto_var "merge_root" in
    let dest_env, dest_root = bind_term dest_env root_name dest_env.location false in
    push_job (left_root, right_root, dest_root);

    (* All bound types are kept, so remember that we know how these are mapped. *)
    let type_triples = fold_types top (fun ps p _ _ -> (p, p, p) :: ps) [] in
    List.iter remember_triple type_triples;

    (* If the user requested that part of the merge be solved in a certain way,
     * through type annotations, we should subtract from each of the
     * sub-environments the expected type annotations, and put them in the
     * destination environment already. *)
    let dest_env, dest_root, left_env, right_env =
      match annot with
      | None ->
          dest_env, dest_root, left_env, right_env
      | Some annot ->
          Log.debug ~level:4 "[make_base] annot: %a" TypePrinter.ptype (top, annot);

          let sub_annot env root =
            match Permissions.sub env root annot with
            | None ->
                let open TypeErrors in
                raise_error env (ExpectedType (annot, root))
            | Some env ->
                env
          in
          let left_env = sub_annot left_env left_root in
          let right_env = sub_annot right_env right_root in
          let dest_env = Permissions.add dest_env dest_root annot in

          dest_env, dest_root, left_env, right_env
    in
    dump_envs left_env right_env dest_env;

    (* In order to properly detect exclusive resource allocation conflicts, we
     * mark those points that have non-duplicable permissions. *)
    let mark_duplicable_points env =
      fold_terms env (fun env point _head { permissions; _ } ->
        if List.exists (fun x -> not (FactInference.is_duplicable env x)) permissions then
          mark env point
        else
          env
      ) env
    in

    let left_env = mark_duplicable_points left_env in
    let right_env = mark_duplicable_points right_env in
    dest_env, dest_root, left_env, right_env

  in

  let dest_env, dest_root, left_env, right_env = make_base_envs ?annot () in

  (* This function, assuming the [left_point, right_point, dest_point] triple is
   * legal, will do a cross-product of [merge_type], trying as it goes to match
   * permissions together and subtract them from their environments. *)
  let rec merge_points
      ((left_env, left_point): env * point)
      ((right_env, right_point): env * point)
      ((dest_env, dest_point): env * point): env * env * env
    =

    Log.debug ~level:3 "[merge_points] %a / %a / %a."
      TypePrinter.pnames (left_env, get_names left_env left_point)
      TypePrinter.pnames (right_env, get_names right_env right_point)
      TypePrinter.pnames (dest_env, get_names dest_env dest_point);

    let left_env = locate left_env (List.hd (get_locations left_env left_point)) in
    let right_env = locate right_env (List.hd (get_locations right_env right_point)) in

    match what_should_i_do (left_env, left_point) (right_env, right_point) (dest_env, dest_point) with
    | Abort ->
        (* Can't process the job, do nothing. *)
        left_env, right_env, dest_env

    | MergeWith dest_point' ->
        (* The oracle told us to merge. Do it. *)
        let dest_env = Permissions.unify dest_env dest_point' dest_point in
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
                merge_type (left_env, left_perm) (right_env, right_perm) ~dest_point dest_env
              in

              begin match Hml_List.take works right_perms with
              | Some (right_perms, (right_perm, (left_env, right_env, dest_env, dest_perm))) ->

                  Log.debug ~level:4 "  → this merge between %a and %a was succesful (got: %a)"
                    TypePrinter.pvar (left_env, get_name left_env left_point)
                    TypePrinter.pvar (right_env, get_name right_env right_point)
                    TypePrinter.ptype (dest_env, dest_perm);

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

        (* We can't just brutally replace the list of permissions using
         * [replace_term], because there are some permissions already for
         * [dest_point] in [dest_env]: at least [=dest_point], but maybe more,
         * depending on user-provided type annotations. *)
        let dest_env = List.fold_left
          (fun dest_env t -> Permissions.add dest_env dest_point t)
          dest_env
          dest_perms
        in
        left_env, right_env, dest_env

  (* end merge_points *)

  (* This is the core of the merge algorithm: this is where we compare a type
   * from the left with a type from the right and decide how to merge the two
   * together. The destination point may not be always present (e.g. in the
   * point-to-point strategy) but is useful for figuring out whether we should
   * just forget about whatever we're doing in case the user provided type
   * annotations. *)
  and merge_type
      ((left_env, left_perm): env * typ)
      ((right_env, right_perm): env * typ)
      ?(dest_point: point option)
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
          let name = fresh_auto_var "merge_point" in
          let dest_env, dest_p = bind_term dest_env name left_env.location false in
          let dest_env = add_location dest_env dest_p right_env.location in
          push_job (left_p, right_p, dest_p);
          Log.debug ~level:4
            "  [push_job] %a / %a / %a"
            TypePrinter.pnames (left_env, get_names left_env left_p)
            TypePrinter.pnames (right_env, get_names right_env right_p)
            TypePrinter.pnames (dest_env, get_names dest_env dest_p);
          dest_env, dest_p
    in

    let has_nominal_type_annotation dest_env dest_point t_dest =
      List.exists (fun t ->
        match is_tyapp t with
        | Some (cons, _args) ->
            same dest_env t_dest cons
        | None ->
            false
      ) (get_permissions dest_env dest_point)
    in

    let has_datacon_type_annotation dest_env dest_point datacon =
      Hml_List.find_opt (fun t ->
        match t with
        | TyConcreteUnfolded (datacon', fields, annot) when Datacon.equal datacon datacon' ->
            Some (fields, annot)
        | _ ->
            None
      ) (get_permissions dest_env dest_point)
    in

    let has_tuple_type_annotation dest_env dest_point =
      Hml_List.find_opt (fun t ->
        match t with
        | TyTuple ts ->
            Some ts
        | _ ->
            None
      ) (get_permissions dest_env dest_point)
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

      (* Structural strategy. This must come first, as we need to learn about
       * pre-allocated destination points in structural types, because of type
       * annotations. *)
      lazy begin
        match left_perm, right_perm with
        | TyConcreteUnfolded (datacon_l, fields_l, clause_l), TyConcreteUnfolded (datacon_r, fields_r, clause_r) ->
            let t_left: point = type_for_datacon left_env datacon_l in
            let t_right: point = type_for_datacon right_env datacon_r in
            let dest_point = Option.extract dest_point in

            if Datacon.equal datacon_l datacon_r then
              (* We need to use a potential type annotation here, so if we
               * already have some information in the destination environment,
               * use it! This is exercised by
               * [test_constraints_in_patterns2.mz] *)
              let annotation = has_datacon_type_annotation dest_env dest_point datacon_l in
              let fields_annot, clause_annot = match annotation with
                | None ->
                    List.map (function
                      | FieldValue (name, _) ->
                          name, None
                      | _ ->
                          assert false
                    ) fields_l, None
                | Some (fields, clause) ->
                    List.map (function
                      | FieldValue (name, t) ->
                          name, Some t
                      | _ ->
                          assert false
                    ) fields, if equal top clause ty_bottom then None else Some clause
              in
              (* Same constructors: both are in expanded form so just schedule the
               * points in their fields for merging. *)
              let dest_env, dest_fields =
                Hml_List.fold_left3 (fun (dest_env, dest_fields) field_l field_r field_annot ->
                  match field_l, field_r, field_annot with
                  | FieldValue (name_l, TySingleton (TyPoint left_p)),
                    FieldValue (name_r, TySingleton (TyPoint right_p)),
                    (name_annot, annot) ->
                      Log.check (Field.equal name_l name_r) "Not in order?";
                      Log.check (Field.equal name_l name_annot) "Not in order?";
                      let dest_env, dest_p = match annot with
                        | Some (TySingleton (TyPoint dest_p)) ->
                            push_job (left_p, right_p, dest_p);
                            dest_env, dest_p
                        | Some _ ->
                            assert false
                        | None ->
                            bind_merge dest_env left_p right_p
                      in
                      (dest_env, FieldValue (name_l, ty_equals dest_p) :: dest_fields)
                  | _ ->
                      Log.error "All permissions should be in expanded form."
                ) (dest_env, []) fields_l fields_r fields_annot
              in
              let r = match clause_annot with
                | Some clause ->
                    Log.check (equal top clause ty_bottom)
                      "If the clause is other than bottom, this means the type \
                      is exclusive, and we provided a type annotation for it. \
                      Since we subtract type annotations early on, left_perm and \
                      right_perm should be gone already!";
                    (* Don't be smart. If we're here, the initial set of expected
                     * permissions was successfully extracted, so keep what the
                     * user specified. *)
                    Some (left_env, right_env, dest_env, clause)
                | None ->
                    let open TypeErrors in
                    try
                      let clause_l = clean top left_env clause_l in
                      let clause_r = clean top right_env clause_r in
                      (* We don't want to be smart here, because
                       * i) the type is not in expanded form and I'm not sure
                       * what it means for it be merged in closed form and
                       * ii) the user had to annotate, so they could at least
                       * annotate properly! *)
                      if not (equal top clause_l clause_r) then
                        raise_error top (NotMergingClauses (left_env, left_perm, clause_l, right_env, right_perm, clause_r))
                      else
                        (* Recursively merge the clause (covariant). *)
                        merge_type (left_env, clause_l) (right_env, clause_r) dest_env
                    with UnboundPoint ->
                      raise_error top (NotMergingClauses (left_env, left_perm, clause_l, right_env, right_perm, clause_r))
              in
              r >>= fun (left_env, right_env, dest_env, clause) ->
              Some (left_env, right_env, dest_env, TyConcreteUnfolded (datacon_l, List.rev dest_fields, clause))


            else if same dest_env t_left t_right then begin
              (* Same nominal type (e.g. [Nil] vs [Cons]). The procedure here is a
               * little bit more complicated. We need to take the nominal type (e.g.
               * [list]), and apply it to [a] flexible on both sides, allocate [a]
               * in [dest_env] and add the relevant triples in [known_triples].
               * Then, perform [Nil - list a] and [Cons - list a]. Then recursively
               * merge the variables pairwise, and if it's still flexible,
               * generalize (or maybe not?).
               *)
              let t_dest = t_left in

              (* Ok, if the user already told us how to fold this type, then
               * don't bother doing the work at all. Otherwise, complain. *)
              if has_nominal_type_annotation dest_env dest_point t_dest then begin
                None
              end else begin
                if get_arity dest_env t_dest > 0 then begin
                  let open TypeErrors in
                  let error = UncertainMerge dest_point in
                  if !Options.pedantic then
                    raise_error dest_env error
                  else
                    Log.warn "%a" print_error (dest_env, error)
                end;

                Log.debug ~level:4 "[cons_vs_cons] left";
                let left_env, t_app_left =
                  build_flexible_type_application (left_env, left_perm) (dest_env, t_dest)
                in
                Log.debug ~level:4 "[cons_vs_cons] right";
                let right_env, t_app_right =
                  build_flexible_type_application (right_env, right_perm) (dest_env, t_dest)
                in

                (* Did the subtractions succeed? *)
                left_env >>= fun left_env ->
                right_env >>= fun right_env ->

                Log.debug ~level:3 "[cons_vs_cons] subtractions performed, got: %a vs %a"
                  TypePrinter.ptype (left_env, t_app_left)
                  TypePrinter.ptype (right_env, t_app_right);

                let r = merge_type (left_env, t_app_left) (right_env, t_app_right) ~dest_point dest_env in
                r >>= fun (left_env, right_env, dest_env, dest_perm) ->
                let dest_perm = Flexible.generalize dest_env dest_perm in
                Some (left_env, right_env, dest_env, dest_perm)
              end

            end else
              None

        | TyTuple ts_l, TyTuple ts_r when List.length ts_l = List.length ts_r ->

            let dest_point = Option.extract dest_point in
            let ts_d = match has_tuple_type_annotation dest_env dest_point with
              | Some ts ->
                  List.map (fun ts -> Some ts) ts
              | None ->
                  Hml_List.make (List.length ts_l) (fun _ -> None)
            in

            let dest_env, dest_points =
              Hml_List.fold_left3 (fun (dest_env, dest_points) t_l t_r t_d ->
                let left_p = !!=t_l in
                let right_p = !!=t_r in
                match t_d with
                | Some (TySingleton (TyPoint dest_p)) ->
                    (* We still need to schedule this job, because we may have a
                     * partial type annotation for one of the tuple components.
                     * Think of it as a job whose destination point has been
                     * pre-allocated!. *)
                    push_job (left_p, right_p, dest_p);
                    (dest_env, dest_p :: dest_points)
                | Some _ ->
                    assert false
                | None ->
                    let dest_env, dest_point = bind_merge dest_env left_p right_p in
                    (dest_env, dest_point :: dest_points)
              ) (dest_env, []) ts_l ts_r ts_d
            in
            let dest_points = List.rev dest_points in
            let ts = List.map ty_equals dest_points in
            Some (left_env, right_env, dest_env, TyTuple ts)

        | _ ->
            None
      end;


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
            merge_type (left_env, left_perm) (right_env, right_perm) ?dest_point dest_env
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
            merge_type (left_env, left_perm) (right_env, right_perm) ?dest_point dest_env
        | _ ->
            None
      end;


      (* Point-to-point strategy.
       *
       * This covers the following cases. Greek letters are flexible variables.
       * - int vs int
       * - int vs float
       * - x vs y
       * - α vs int
       * - α vs β *)
      lazy begin
        match left_perm, right_perm with
        | TyPoint left_p, TyPoint right_p ->
            Log.check (is_type left_env left_p && is_type right_env right_p
              || is_term left_env left_p && is_term right_env right_p)
              "Sanity check failed";

            let flex_left = is_flexible left_env left_p
            and flex_right = is_flexible right_env right_p in
            let left_p = PersistentUnionFind.repr left_p left_env.state in
            let right_p = PersistentUnionFind.repr right_p right_env.state in
            Log.debug "  [p2p] %b, %b" flex_left flex_right;

            begin match flex_left, flex_right with
            | false, false ->
                if is_type left_env left_p then begin
                  (* Type vs type. *)

                  (* This could happen because a function has return type:
                   *   ∃(t::★). ...
                   * and after calling that function in one of the
                   * sub-environments, we opened [t] in the local environment. *)
                  if not (valid dest_env left_p) || not (valid dest_env right_p) then
                    Log.error "Local types are not supported yet";

                  if not (same dest_env left_p right_p) then
                    (* e.g. [int] vs [float] *)
                    None
                  else
                    (* e.g. [int] vs [int] *)
                    Some (left_env, right_env, dest_env, TyPoint left_p)
                end else begin
                  (* Term vs term *)
                  let dest_env, dest_p = bind_merge dest_env left_p right_p in
                  Some (left_env, right_env, dest_env, TyPoint dest_p)
                end

            | false, true ->
                let dest_p = PersistentUnionFind.repr left_p left_env.state in

                (* This eliminates the case where [left_p] is a variable with a
                 * structure that makes no sense in the destination environment.
                 * Typically, a flexible variable that was instanciated with
                 * [=x], [x] being local to the left environment. *)
                if is_valid top left_env left_perm then begin

                  (* This must be a top-level type and [left_p] must be valid in the
                   * destination environment. *)
                  Log.check (is_type dest_env dest_p) "A flexible variable must refer \
                    to a type defined in the top-level scope, we don't know how to treat \
                    flexible variables with kind other than type yet.";

                  let right_env = merge_left right_env dest_p right_p in
                  Log.check (is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p))
                    "All top-level types should be in known_triples by default";

                  Some (left_env, right_env, dest_env, TyPoint dest_p)

                end else
                  None

            | true, false ->
                let dest_p = PersistentUnionFind.repr right_p right_env.state in

                if is_valid top right_env right_perm then begin

                  (* This must be a top-level type and [right_p] must be valid in the
                   * destination environment. *)
                  Log.check (is_type dest_env dest_p) "A flexible variable must refer \
                    to a type defined in the top-level scope, we don't know how to treat \
                    flexible variables with kind other than type yet.";

                  let left_env = merge_left left_env dest_p left_p in
                  Log.check (is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p))
                    "All top-level types should be in known_triples by default";

                  Some (left_env, right_env, dest_env, TyPoint dest_p)

                end else
                  None

            | true, true ->
                let k = get_kind left_env left_p in
                Log.check (k = get_kind right_env right_p) "Kinds inconsistent!";

                begin match merge_candidate (left_env, left_p) (right_env, right_p) with
                | Some dest_p ->
                    Some (left_env, right_env, dest_env, TyPoint dest_p)
                | None ->
                    Log.check (k <> KTerm) "Remove this when we have a testcase, \
                      and try to understand what's happening, and whether it's \
                      correct!";

                    let dest_env, dest_p =
                      bind_var dest_env ~flexible:true (get_name left_env left_p, k, dest_env.location)
                    in
                    remember_triple (left_p, right_p, dest_p);

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

        | TyConcreteUnfolded (datacon_l, _, _), _ ->
            let t_left = type_for_datacon left_env datacon_l in
            let t_dest = t_left in

            let left_env, t_app_left =
              build_flexible_type_application (left_env, left_perm) (dest_env, t_dest)
            in

            left_env >>= fun left_env ->
            merge_type (left_env, t_app_left) (right_env, right_perm) ?dest_point dest_env


        | _, TyConcreteUnfolded (datacon_r, _, _) ->
            let t_right = type_for_datacon right_env datacon_r in
            let t_dest = t_right in

            let right_env, t_app_right =
              build_flexible_type_application (right_env, right_perm) (dest_env, t_dest)
            in

            right_env >>= fun right_env ->
            merge_type (left_env, left_perm) (right_env, t_app_right) ?dest_point dest_env


        | TyApp (consl, argsl), TyApp (consr, argsr) ->
            (* Merge the constructors. This should be a no-op, unless they're
             * distinct, in which case we stop here. *)
            let r = merge_type (left_env, consl) (right_env, consr) ?dest_point dest_env in
            r >>= fun (left_env, right_env, dest_env, cons) ->

            let cons = !!cons in

            if has_nominal_type_annotation dest_env (Option.extract dest_point) cons then
              None
            else
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
                  match variance dest_env cons i with
                  | Covariant ->
                      merge_type (left_env, argl) (right_env, argr) ?dest_point dest_env
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
              let t = ty_app (TyPoint cons) args in

              (* And we're good to go. *)
              Some (left_env, right_env, dest_env, t)

        | _ ->
            None
      end;

    ] in

    Hml_List.find_opt Lazy.force strategies

  (* end merge_types *)

  (* This just says: if on one side there is a flexible variable, and the other
   * side makes sense in the destination environment, instantiate the flexible
   * variable. *)
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
          None
        end

    | t, TyPoint p when is_flexible right_env p ->
        begin try
          let t = clean top left_env t in
          let right_env = instantiate_flexible right_env p t in
          Some (left_env, right_env, dest_env, t)
        with UnboundPoint ->
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

  Permissions.safety_check dest_env;

  (* So return it. *)
  dest_env, dest_root
;;


let merge_envs (top: env) ?(annot: typ option) (left: env * point) (right: env * point): env * point =
  if (fst left).inconsistent then
    right
  else if (fst right).inconsistent then
    left
  else
    actually_merge_envs top ?annot left right
;;
