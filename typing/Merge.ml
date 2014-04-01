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

open Kind
open TypeCore
open Types
open Either

type t = (env * var) * (var list * var list * var list)

type outcome = MergeWith of var | Proceed | Abort

(* The logic is the same on both sides, but I'm writing this with
 * the left-side in mind. *)
let build_flexible_type_application (left_env, left_perm) (dest_env, t_dest) =
  (* First, find the definition of the type so that we know how to
   * instanciate parameters. *)
  let left_env, arg_vars_l = make_datacon_letters left_env (get_kind dest_env t_dest) true in
  let t_app_left = ty_app (TyOpen t_dest) (List.map (fun x -> TyOpen x) arg_vars_l) in
  (* Chances are this will perform a merge in [left_env]: this is why
   * we're returning [left_env]. *)
  let left_env = Permissions.sub_type left_env left_perm t_app_left in
  left_env |> Permissions.drop_derivation, t_app_left
;;


let is_valid top sub t =
  try
    ignore (clean top sub t);
    true
  with UnboundPoint ->
    false
;;



module Lifo = struct
  let create () = ref [];;
  let pop r = let v = List.hd !r in r := List.tl !r; v;;
  let push r v = r := v :: !r;;
  let remove r v =
    match MzList.take (fun v' -> if v = v' then Some () else None) !r with
    | Some (remaining, _) ->
        r := remaining
    | None ->
        assert false
  ;;
end

let actually_merge_envs (top: env) ?(annot: typ option) (left: env * var) (right: env * var): t =
  (* We use a work list (a LIFO) to schedule vars for merging. This implements
   * a depth-first traversal of the graph, which is indeed what we want (for the
   * moment). *)
  let pending_jobs = Lifo.create () in

  (* One invariant is that if you push a job, the job's destination var has
   * been allocated in the destination environment already. *)
  let push_job = Lifo.push pending_jobs in
  let pop_job () = Lifo.pop pending_jobs in

  (* We also keep a list of [left_var, right_var, dest_var] triples that
   * have been processed already. *)
  let known_triples = Lifo.create () in
  let remember_triple = Lifo.push known_triples in
  let _forget_triple = Lifo.remove known_triples in
  let dump_known_triples left_env right_env dest_env =
    let open TypePrinter in
    List.iter (fun (left_var, right_var, dest_var) ->
      Log.debug ~level:3 "%a / %a / %a"
        pnames (left_env, get_names left_env left_var)
        pnames (right_env, get_names right_env right_var)
        pnames (dest_env, get_names dest_env dest_var)) !known_triples;
      Log.debug "";
  in

  (* If one of our jobs is based on [left_var] and [right_var], we may have
   * mapped these two to a var in the destination environment already. *)
  let merge_candidate (left_env, left_var) (right_env, right_var): var option =
    let merge_candidates = List.filter
      (fun (left_var', right_var', _) ->
        same left_env left_var left_var' &&
        same right_env right_var right_var')
      !known_triples
    in
    Log.check (List.length merge_candidates <= 1)
      "The list of known triples is not consistent";
    match merge_candidates with
    | [_, _, dest_var'] -> Some dest_var'
    | _ -> None
  in

  let is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p) =
    match merge_candidate (left_env, left_p) (right_env, right_p) with
    | Some dest_p' ->
        same dest_env dest_p dest_p'
    | None ->
        false
  in

  let left_conflicts: var list ref = ref [] in
  let right_conflicts: var list ref = ref [] in
  let dest_conflicts: var list ref = ref [] in

  (* This oracle decides what to do with a given job. There are three outcomes:
    - we've already mapped the left and right vars to a certain var in the
      destination environment: just merge the desired var with the one that's
      been mapped already → this strategy tries to preserve sharing;
    - the destination var appears in [known_triples] already: we've already
      merged this var, don't touch it anymore;
    - there's no such thing: perform the merge operation with the triple.

    We can map a var from [left_env] or [right_env] to several vars in
    [dest_env] but for a given var in [dest_env], only ONE var from
    [left_env] (resp. [right_var]) vars to it.
  *)
  let what_should_i_do
      (left_env, left_var)
      (right_env, right_var)
      (dest_env, dest_var): outcome
    =

    match merge_candidate (left_env, left_var) (right_env, right_var) with
    | Some dest_var' ->
        (* We can share! *)
        Log.debug ~level:3 "[oracle] merge job %a → %a"
          TypePrinter.pnames (dest_env, get_names dest_env dest_var)
          TypePrinter.pnames (dest_env, get_names dest_env dest_var');
        MergeWith dest_var'

    | None ->
        (* Try to see if we've processed this var already. *)
        let same_dest = List.filter (fun (_, _, dest_var') ->
          same dest_env dest_var dest_var') !known_triples
        in
        Log.check (List.length same_dest <= 1) "The list of known triples is not consistent";

        (* Because [merge_candidates] returned [None], we know that we're not in
         * a case of sharing. So if one of the two checks below succeeds, this
         * means that we've visited either the left var with a different path
         * on the right side, or the converse. If the var is marked (and
         * [make_base_envs] marked those vars that originally contained a
         * non-duplicable permission), then we're in a case of exclusive
         * resource allocation conflict: we're trying to use, say, the same
         * left_var for a different right_var. *)
        begin match MzList.find_opt (fun (l, _, _) ->
          if same left_env left_var l && is_marked left_env l then
            Some l
          else
            None
        ) !known_triples with
        | Some l ->
            let open TypeErrors in
            let error = ResourceAllocationConflict left_var in
            may_raise_error left_env error;
            (* Highlight all the variables involved in the conflict. *)
            left_conflicts := l :: !left_conflicts;
            right_conflicts := right_var :: (MzList.map_some (fun (l', r, _) ->
              if same left_env l l' then Some r else None
            ) !known_triples) @ !right_conflicts;
            dest_conflicts := dest_var :: (MzList.map_some (fun (l', _, d) ->
              if same left_env l l' then Some d else None
            ) !known_triples) @ !dest_conflicts;
        | None ->
            ()
        end;
        begin match MzList.find_opt (fun (_, r, _) ->
          if same right_env right_var r && is_marked right_env r then
            Some r
          else
            None
        ) !known_triples with
        | Some r ->
            let open TypeErrors in
            let error = ResourceAllocationConflict right_var in
            may_raise_error right_env error;
            right_conflicts := r :: !right_conflicts;
            left_conflicts := left_var :: (MzList.map_some (fun (l, r', _) ->
              if same left_env r r' then Some l else None
            ) !known_triples) @ !left_conflicts;
            dest_conflicts := dest_var :: (MzList.map_some (fun (_, r', d) ->
              if same right_env r r' then Some d else None
            ) !known_triples) @ !dest_conflicts;
        | None ->
            ()
        end;


        if List.length same_dest = 0 then begin
          (* Remember the triple. *)
          remember_triple (left_var, right_var, dest_var);

          Log.debug ~level:3 "[oracle] processing job %a / %a / %a."
            TypePrinter.pnames (left_env, get_names left_env left_var)
            TypePrinter.pnames (right_env, get_names right_env right_var)
            TypePrinter.pnames (dest_env, get_names dest_env dest_var);
          Proceed

        end else begin
          Log.debug ~level:4 "[oracle] discarding job since %a has been visited already"
            TypePrinter.pnames (dest_env, get_names dest_env dest_var);

          (* This piece of code is actually dead because we always allocate a
           * fresh (existentially-quantified) var in the destination
           * environment. This means we always call this function with
           * [dest_var] fresh, which means there's no way we processed it
           * already. *)
          if true then assert false;

          (* Do nothing, since it would be illegal! *)
          Abort

        end
  in


  let dump_envs left_env right_env dest_env =

    Log.debug ~level:3 "\n------------ LEFT --------------\n\n%a"
      MzPprint.pdoc (TypePrinter.print_permissions, left_env);

    Log.debug ~level:3 "\n------------ RIGHT -------------\n\n%a"
      MzPprint.pdoc (TypePrinter.print_permissions, right_env);

    Log.debug ~level:3 "\n------------ DEST -------------\n\n%a"
      MzPprint.pdoc (TypePrinter.print_permissions, dest_env);

    Log.debug ~level:3 "\n--------------------------------\n";

  in


  let make_base_envs ?annot () =

    Log.debug ~level:3 "\n--------- START MERGE @ %a (annot: %b) ----------\n\n%a\n\n"
      Lexer.p (location top)
      (annot <> None)
      MzPprint.pdoc (TypePrinter.print_permissions, top);

    let is_external var =
      let names = get_names top var in
      List.exists (function
        | User (mname, _) when not (Module.equal (module_name top) mname) ->
            true
        | _ ->
            false
      ) names
    in

    (* This is the destination environment; it will evolve over time. Initially,
     * it is empty. As an optimization, we keep the vars that were previously
     * defined so that the mapping is the identity for all the vars from [top]. *)
    let dest_env = fold_terms top (fun dest_env var _ ->
      if not (is_external var) then
        reset_permissions dest_env var
      else
        dest_env
    ) top in
    let dest_env = set_floating_permissions dest_env [] in

    (* TODO we should iterate over all pairs of roots here, and see if they've
     * been merged in both sub-environments. In that case, they should be merged
     * beforehand in the destination environment too. Merges in local
     * sub-environments can happen because a dynamic == test refined the
     * permissions. *)

    (* All the roots should be merged. *)
    let roots = fold_terms top (fun acc k _ -> k :: acc) [] in
    List.iter (fun p -> if not (is_external p) then push_job (p, p, p)) roots;

    (* Create an additional root for the result of the match. Schedule it for
     * merging, at the front of the list (this implements our first heuristic). *)
    let left_env, left_root = left in
    let right_env, right_root = right in
    let root_name = fresh_auto_name "merge_root" in
    let dest_env, dest_root = bind_rigid dest_env (root_name, KTerm, location dest_env) in
    push_job (left_root, right_root, dest_root);

    (* All bound types are kept, so remember that we know how these are mapped. *)
    let type_triples = fold top (fun ps p ->
      if is_type top p then
        (p, p, p) :: ps
      else
        ps
    ) [] in
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
            | Right d ->
                let open TypeErrors in
                raise_error env (ExpectedType (annot, root, d))
            | Left (env, _) ->
                env
          in
          let left_env = sub_annot left_env left_root in
          let right_env = sub_annot right_env right_root in
          let dest_env = Permissions.add dest_env dest_root annot in

          dest_env, dest_root, left_env, right_env
    in
    dump_envs left_env right_env dest_env;

    (* In order to properly detect exclusive resource allocation conflicts, we
     * mark those vars that have non-duplicable permissions. *)
    let mark_duplicable_vars env =
      let env = refresh_mark env in
      fold_terms env (fun env var permissions ->
        if List.exists (fun x -> not (FactInference.is_duplicable env x)) permissions then
          mark env var
        else
          env
      ) env
    in

    let left_env = mark_duplicable_vars left_env in
    let right_env = mark_duplicable_vars right_env in
    dest_env, dest_root, left_env, right_env

  in

  let dest_env, dest_root, left_env, right_env = make_base_envs ?annot () in

  (* This function, assuming the [left_var, right_var, dest_var] triple is
   * legal, will do a cross-product of [merge_type], trying as it goes to match
   * permissions together and subtract them from their environments. *)
  let rec merge_vars
      ((left_env, left_var): env * var)
      ((right_env, right_var): env * var)
      ((dest_env, dest_var): env * var): env * env * env
    =

    Log.debug ~level:3 "[merge_vars] %a / %a / %a."
      TypePrinter.pnames (left_env, get_names left_env left_var)
      TypePrinter.pnames (right_env, get_names right_env right_var)
      TypePrinter.pnames (dest_env, get_names dest_env dest_var);

    let left_env = locate left_env (List.hd (get_locations left_env left_var)) in
    let right_env = locate right_env (List.hd (get_locations right_env right_var)) in

    match what_should_i_do (left_env, left_var) (right_env, right_var) (dest_env, dest_var) with
    | Abort ->
        (* Can't process the job, do nothing. *)
        left_env, right_env, dest_env

    | MergeWith dest_var' ->
        (* The oracle told us to merge. Do it. *)
        let dest_env = Permissions.unify dest_env dest_var' dest_var in
        left_env, right_env, dest_env

    | Proceed ->

        if is_flexible left_env left_var || is_flexible right_env right_var then
          match merge_type (left_env, TyOpen left_var) (right_env, TyOpen right_var) dest_env with
          | Some (left_env, right_env, dest_env, _dest_type) ->
              left_env, right_env, dest_env
          | None ->
              Log.error "FIXME wicked wicked case"

        else
          let left_perms = get_permissions left_env left_var in
          let right_perms = get_permissions right_env right_var in
          let left_env, left_perms, right_env, right_perms, dest_env, dest_perms =
            merge_lists
              (left_env, left_perms, [])
              (right_env, right_perms)
              ~dest_var (dest_env, [])
          in

          let left_env =
            set_permissions left_env left_var left_perms
          in
          let right_env =
            set_permissions right_env right_var right_perms
          in

          (* We can't just brutally replace the list of permissions using
           * [replace_term], because there are some permissions already for
           * [dest_var] in [dest_env]: at least [=dest_var], but maybe more,
           * depending on user-provided type annotations. *)
          let dest_env = List.fold_left
            (fun dest_env t -> Permissions.add dest_env dest_var t)
            dest_env
            dest_perms
          in
          left_env, right_env, dest_env

  (* end merge_vars *)

  (* This function will take an initially empty [dest_perms] and try
    combinations pairwise from [left_perms] and [right_perms] to build
    [dest_perms]. It only visits each permission in [left_perms] once, and it
    may consume elements from [remaining_right_perms] as it goes.

    After a permission from [left_perms] has been tried, if the merge didn't
    succeed or if the permission was duplicable, it goes into
    [processed_left_perms] so that it remains available afterwards. Otherwise,
    if the merge suceeded and the permission wasn't duplicable, it is discarded.
    
    This function returns the remaining permissions for both [left] and [right]. *)
  and merge_lists
      (left_env, left_perms, processed_left_perms)
      (right_env, remaining_right_perms)
      ?dest_var
      (dest_env, dest_perms): env * (typ list) * env * (typ list) * env * (typ list) =
    (* [left_perms] and [remaining_right_perms] are the remaining permissions that
     * we need to match together. *)
    match left_perms, remaining_right_perms with
    | [], _
    | _, [] ->
        (* Return the permissions left for both the left and the right
         * environment. *)
        left_env, left_perms @ processed_left_perms, right_env, remaining_right_perms, dest_env, dest_perms

    | left_perm :: left_perms, remaining_right_perms ->

        let works right_perm =
          merge_type (left_env, left_perm) (right_env, right_perm) ?dest_var dest_env
        in

        begin match MzList.take works remaining_right_perms with
        | Some (remaining_right_perms, (right_perm, (left_env, right_env, dest_env, dest_perm))) ->

            Log.debug ~level:4 "  → this merge between %a and %a was succesful (got: %a)"
              TypePrinter.ptype (left_env, left_perm)
              TypePrinter.ptype (right_env, right_perm)
              TypePrinter.ptype (dest_env, dest_perm);

            (* We've found a matching pair. Whether [left_perm] and [right_perm]
             * are available afterwards depends on their duplicities. *)
            let left_is_duplicable = FactInference.is_duplicable left_env left_perm in
            let right_is_duplicable = FactInference.is_duplicable right_env right_perm in
            let processed_left_perms =
              if left_is_duplicable then left_perm :: processed_left_perms else processed_left_perms
            in
            let remaining_right_perms =
              if right_is_duplicable then right_perm :: remaining_right_perms else remaining_right_perms
            in

            merge_lists
              (left_env, left_perms, processed_left_perms)
              (right_env, remaining_right_perms)
              ?dest_var
              (dest_env, dest_perm :: dest_perms)

        | None ->
            (* The pair doesn't match. Discard [left_perm] from the list of
             * permissions to try out, but keep it available for later since we
             * didn't consume it. *)
            merge_lists
              (left_env, left_perms, left_perm :: processed_left_perms)
              (right_env, remaining_right_perms)
              ?dest_var
              (dest_env, dest_perms)
        end

  (* end merge_lists *)

  (* This is the core of the merge algorithm: this is where we compare a type
   * from the left with a type from the right and decide how to merge the two
   * together. The destination var may not be always present (e.g. in the
   * var-to-var strategy) but is useful for figuring out whether we should
   * just forget about whatever we're doing in case the user provided type
   * annotations. *)
  and merge_type
      ((left_env, left_perm): env * typ)
      ((right_env, right_perm): env * typ)
      ?(dest_var: var option)
      (dest_env: env): (env * env * env * typ) option
    =

    (* Allocate a new var [dest_p] in [dest_env] and schedule [left_p] and [right_p]
     * for merging with [dest_p]. Return [dest_env, dest_p]. *)
    let bind_merge dest_env left_p right_p =
      (* As a small optimization, if the var we're allocating is about to be
       * merged immediately by [merge_vars], we don't allocate it at all
       * (which means less output, less fresh names, etc.). *)
      match merge_candidate (left_env, left_p) (right_env, right_p) with
      | Some dest_p ->
          dest_env, dest_p
      | None ->
          let name = fresh_auto_name "merge_var" in
          let dest_env, dest_p = bind_rigid dest_env (name, KTerm, location left_env) in
          let dest_env = add_location dest_env dest_p (location right_env) in
          push_job (left_p, right_p, dest_p);
          Log.debug ~level:4
            "  [push_job] %a / %a / %a"
            TypePrinter.pnames (left_env, get_names left_env left_p)
            TypePrinter.pnames (right_env, get_names right_env right_p)
            TypePrinter.pnames (dest_env, get_names dest_env dest_p);
          dest_env, dest_p
    in

    let has_nominal_type_annotation dest_env dest_var t_dest =
      List.exists (fun t ->
        let t = modulo_flex dest_env t in
        let t = expand_if_one_branch dest_env t in
        match is_tyapp t with
        | Some (cons, _args) ->
            same dest_env t_dest cons
        | None ->
            false
      ) (get_permissions dest_env dest_var)
    in

    let open TypePrinter in
    Log.debug ~level:4
      "  [merge_type] %a with %a"
      ptype (left_env, left_perm)
      ptype (right_env, right_perm);

    let left_perm = modulo_flex left_env left_perm in 
    let right_perm = modulo_flex right_env right_perm in 

    let is_local_left left_p =
      not (is_valid dest_env left_env (TyOpen left_p))
    and is_local_right right_p =
      not (is_valid dest_env right_env (TyOpen right_p))
    in

    (* Because the order is important, we try various "strategies" that attempt
     * to solve this merge problem. A strategy just returns an option: if it
     * didn't work, we just try the next strategy. If all strategies fail, this
     * means we can't merge these two types together! Thankfully, [merge_vars]
     * knows how to deal with that. *)
    let strategies = [

      (* Simple equals strategy.
       *
       * TEMPORARY: the call to "equal" is just a syntactic check; this is not a
       * powerful tool, and we may want to merge things in a more sophisticated
       * way. What about merging two functions that have slightly different, but
       * compatible types? There is no case below that deals with function
       * types, and still, we should be able to merge them. Instead of doing a
       * simple call to [equal], we should do:
       *
       * if valid top left_perm && valid top right_perm then
       *   sub_type dest_env left_perm right_perm >>=
       *   sub_type dest_env right_perm left_perm >>=
       *   Some (left_env, right_env, dest_env, left_perm)
       * else
       *   None
       *
       * But this may be too expensive... need to think about it more (in the
       * meanwhile, read tests/merge-func.mz).
       *)
      lazy begin
        try
          let left_perm = clean left_env left_env left_perm in
          let right_perm = clean right_env right_env right_perm in
          if equal top left_perm right_perm then begin
            Log.debug ~level:5 "→ fast_path, the types are equal in the original environment, \
              don't touch them";
            Some (left_env, right_env, dest_env, left_perm)
          end else begin
            None
          end
        with UnboundPoint ->
          None
      end;


      (* var-to-var strategy.
       *
       * This covers the following cases. Greek letters are flexible variables.
       * - int vs int
       * - int vs float
       * - x vs y
       * - α vs int
       * - α vs β *)
      lazy begin
        match left_perm, right_perm with
        | TyOpen left_p, TyOpen right_p ->
            Log.check (get_kind left_env left_p = get_kind right_env right_p)
              "Sanity check failed";

            let flex_left = is_flexible left_env left_p
            and flex_right = is_flexible right_env right_p in
            Log.debug ~level:5 "  [p2p] %b, %b" flex_left flex_right;

            begin match flex_left, flex_right with
            | false, false ->
                if is_type left_env left_p || is_perm left_env left_p then begin
                  (* Type vs type, perm vs perm *)

                  (* This could happen because a function has return type:
                   *   ∃(t::★). ...
                   * and after calling that function in one of the
                   * sub-environments, we opened [t] in the local environment. *)
                  let is_local_type =
                    is_local_left left_p || is_local_right right_p
                  in
                  if is_local_type then begin
                    let open TypeErrors in
                    may_raise_error top LocalType
                  end;

                  if is_local_type || not (same dest_env left_p right_p) then
                    (* e.g. [int] vs [float], or [t] vs [float] *)
                    None
                  else
                    (* e.g. [int] vs [int] *)
                    Some (left_env, right_env, dest_env, TyOpen left_p)
                end else begin
                  (* Term vs term *)
                  let dest_env, dest_p = bind_merge dest_env left_p right_p in
                  Some (left_env, right_env, dest_env, TyOpen dest_p)
                end

            | false, true ->
                let dest_p = left_p in

                (* This must be a top-level type and [left_p] must be valid in the
                 * destination environment. *)
                Log.check (not (is_local_left left_p) && is_type dest_env dest_p) "A flexible variable must refer \
                  to a type defined in the top-level scope, we don't know how to treat \
                  flexible variables with kind other than type yet.";

                (* This is the same as above: we don't know how to merge a
                 * local type variable, and we don't want to repack. *)
                if is_valid top left_env left_perm then begin

                  (* From now on, we decide that [right_p], a flexible variable
                   * on the right-hand-side, is instantiated to [dest_p], a type
                   * that is known to be valid in [top], hence in [right_env].
                   * *)
                  merge_left right_env dest_p right_p >>= fun right_env ->
                  Log.check (is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p))
                    "All top-level types should be in known_triples by default";

                  Some (left_env, right_env, dest_env, TyOpen dest_p)

                end else
                  None

            | true, false ->
                let dest_p = right_p in

                (* See above *)
                Log.check (not (is_local_right right_p) && is_type dest_env dest_p) "A flexible variable must refer \
                  to a type defined in the top-level scope, we don't know how to treat \
                  flexible variables with kind other than type yet.";

                if is_valid top right_env right_perm then begin

                  merge_left left_env dest_p left_p >>= fun left_env ->
                  Log.check (is_known_triple (left_env, left_p) (right_env, right_p) (dest_env, dest_p))
                    "All top-level types should be in known_triples by default";

                  Some (left_env, right_env, dest_env, TyOpen dest_p)

                end else
                  None

            | true, true ->
                let k = get_kind left_env left_p in
                Log.check (k = get_kind right_env right_p) "Kinds inconsistent!";

                begin match merge_candidate (left_env, left_p) (right_env, right_p) with
                | Some dest_p ->
                    Some (left_env, right_env, dest_env, TyOpen dest_p)
                | None ->
                    Log.check (k <> KTerm) "Remove this when we have a testcase, \
                      and try to understand what's happening, and whether it's \
                      correct!";

                    let dest_env, dest_p =
                      bind_flexible dest_env (get_name left_env left_p, k, location dest_env)
                    in
                    remember_triple (left_p, right_p, dest_p);

                    Some (left_env, right_env, dest_env, TyOpen dest_p)
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
       * This must come *after* the var-to-var strategy. *)
      lazy begin
        try_merge_flexible (left_env, left_perm) (right_env, right_perm) dest_env
      end;


      (* General strategy. *)
      lazy begin
        match left_perm, right_perm with

        | TyConcrete branch_l, TyConcrete branch_r ->
            let datacon_l = branch_l.branch_datacon
            and datacon_r = branch_r.branch_datacon in
            let t_left: var = !!(fst datacon_l)
            and t_right: var = !!(fst datacon_r) in
            let dest_var = Option.extract dest_var in

            (* We would need to check that the definitions match and merge local
             * definitions into a common definition. I am *SO* not doing that.
             * *)
            if not (is_local_left t_left) && not (is_local_right t_right) then begin

              (* The procedure here is a little bit complicated. We first start by
               * the case where the data constructors are equal (e.g. [Cons] vs
               * [Cons]), then we treat the case where the data constructors
               * belong to the same type (e.g. [Cons] vs [Nil]). *)
              if resolved_datacons_equal dest_env datacon_l datacon_r then
                (* The constructors are equal, so we can start by merging the
                 * fields one-by-one. We assume the fields to be in expanded form,
                 * so we can always call [bind_merge]. *)
                let dest_env, dest_fields =
                  List.fold_left2 (fun (dest_env, dest_fields) (name_l, left_t) (name_r, right_t) ->
                    Log.check (Field.equal name_l name_r) "Not in order?";
                    let dest_env, dest_p = bind_merge dest_env !!=left_t !!=right_t in
                    dest_env, (name_l, ty_equals dest_p) :: dest_fields
                  ) (dest_env, []) branch_l.branch_fields branch_r.branch_fields
                in

                (* Please note that we're building a type "A { fᵢ = xᵢ }" which
                 * may contradict a pre-existing type "A { fᵢ = yᵢ }" for
                 * [dest_var] obtained through a type annotation. That's fine,
                 * though, because the [Permissions] module will use its special
                 * rule to assume "xᵢ = yᵢ". *)
                let dest_fields = List.rev dest_fields in

                (* Finally, we need to merge the "adopts" clause on the structural
                 * types. *)
                let r = 
                  let open TypeErrors in
                  let clause_l = branch_l.branch_adopts
                  and clause_r = branch_r.branch_adopts in
                  try
                    let clause_l = clean top left_env clause_l in
                    let clause_r = clean top right_env clause_r in
                    (* We don't want to be smart here, because:
                     * i) the clause is not in expanded form (no singletons
                     *    everywhere) and the whole [Merge] module makes that
                     *    assumption, so recursively calling [merge_type] would be
                     *    dangerous. I don't understand what
                     *    [merge_type_with_unfolding] would mean in that case
                     *    either (we'd have to re-fold permissions with a [TyBar]?).
                     * ii) it's a good practice to annotate such a tricky case. *)
                    if not (equal top clause_l clause_r) then
                      raise_error top (NotMergingClauses (left_env, left_perm, clause_l, right_env, right_perm, clause_r))
                    else
                      (* Recursively merge the clause (covariant). *)
                      merge_type (left_env, clause_l) (right_env, clause_r) dest_env
                  with UnboundPoint ->
                    raise_error top (NotMergingClauses (left_env, left_perm, clause_l, right_env, right_perm, clause_r))
                in
                r >>= fun (left_env, right_env, dest_env, clause) ->
                let branch = { branch_l with
                  branch_fields = dest_fields;
                  branch_adopts = clause;
                } in
                Some (left_env, right_env, dest_env, TyConcrete branch)


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
                if has_nominal_type_annotation dest_env dest_var t_dest then begin
                  None
                end else begin
                  if get_arity dest_env t_dest > 0 then begin
                    let open TypeErrors in
                    let error = UncertainMerge dest_var in
                    may_raise_error dest_env error
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

                  let r = merge_type (left_env, t_app_left) (right_env, t_app_right) ~dest_var dest_env in
                  r >>= fun (left_env, right_env, dest_env, dest_perm) ->
                  Some (left_env, right_env, dest_env, dest_perm)
                end

              end else
                None
            end else
              None

        | TyTuple ts_l, TyTuple ts_r when List.length ts_l = List.length ts_r ->
            let dest_env, dest_vars =
              List.fold_left2 (fun (dest_env, dest_vars) t_l t_r ->
                let left_p = !!=t_l in
                let right_p = !!=t_r in
                let dest_env, dest_var = bind_merge dest_env left_p right_p in
                (dest_env, dest_var :: dest_vars)
              ) (dest_env, []) ts_l ts_r
            in
            let dest_vars = List.rev dest_vars in
            let ts = List.map ty_equals dest_vars in
            Some (left_env, right_env, dest_env, TyTuple ts)

        | TySingleton left_t, TySingleton right_t ->
            let r = merge_type (left_env, left_t) (right_env, right_t) dest_env in
            r >>= fun (left_env, right_env, dest_env, dest_t) ->
            Some (left_env, right_env, dest_env, TySingleton dest_t)

        | TyConcrete branch_l, _ ->
            let datacon_l = branch_l.branch_datacon in
            let t_left = !!(fst datacon_l) in
            let t_dest = t_left in

            if not (is_local_left t_left) then
              let left_env, t_app_left =
                build_flexible_type_application (left_env, left_perm) (dest_env, t_dest)
              in

              left_env >>= fun left_env ->
              merge_type (left_env, t_app_left) (right_env, right_perm) ?dest_var dest_env
            else
              None


        | _, TyConcrete branch_r ->
            let datacon_r = branch_r.branch_datacon in
            let t_right = !!(fst datacon_r) in
            let t_dest = t_right in

            if not (is_local_right t_right) then
              let right_env, t_app_right =
                build_flexible_type_application (right_env, right_perm) (dest_env, t_dest)
              in

              right_env >>= fun right_env ->
              merge_type (left_env, left_perm) (right_env, t_app_right) ?dest_var dest_env
            else
              None


        | TyApp (consl, argsl), TyApp (consr, argsr)
          when get_kind left_env !!consl = get_kind right_env !!consr
          && not (is_local_left !!consl) && not (is_local_right !!consr) ->
            (* Merge the constructors. This should be a no-op, unless they're
             * distinct, in which case we stop here. *)
            let r = merge_type (left_env, consl) (right_env, consr) ?dest_var dest_env in
            r >>= fun (left_env, right_env, dest_env, cons) ->

            let cons = !!cons in

            if Option.is_some dest_var && has_nominal_type_annotation dest_env (Option.extract dest_var) cons then
              None
            else
              (* So the constructors match. Let's now merge pairwise the arguments. *)
              let r = MzList.fold_left2i (fun i acc argl argr ->
                (* We keep the current triple of environments and the merge
                 * arguments in the accumulator. *)
                acc >>= fun (left_env, right_env, dest_env, args) ->
                let v =
                  (* In the obvious case where one variable is flexible, do the
                   * obvious thing! *)
                  try_merge_flexible (left_env, argl) (right_env, argr) dest_env |||

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
                      merge_type_with_unfolding (left_env, argl) (right_env, argr) ?dest_var dest_env
                  | _ ->
                      begin try
                        let argl = clean top left_env argl in
                        let argr = clean top right_env argr in
                        Permissions.sub_type dest_env argl argr
                        |> Permissions.drop_derivation >>= fun dest_env ->
                        Permissions.sub_type dest_env argr argl
                        |> Permissions.drop_derivation >>= fun dest_env ->
                        Some (left_env, right_env, dest_env, argl)
                      with UnboundPoint ->
                        None
                      end
                in
                v >>= fun (left_env, right_env, dest_env, arg) ->
                (* The parameter was merged. Return a valid accumulator. *)
                Some (left_env, right_env, dest_env, arg :: args)
              ) (Some (left_env, right_env, dest_env, [])) argsl argsr in
              r >>= fun (left_env, right_env, dest_env, args) ->

              (* Yay! All type parameters were merged. Reverse the list. *)
              let args = List.rev args in

              (* Re-fold the type application. *)
              let t = ty_app (TyOpen cons) args in

              (* And we're good to go. *)
              Some (left_env, right_env, dest_env, t)

        | _ ->
            None
      end;

      (* If nothing else worked we can still make progress by expanding eagerly
       * type abbreviations. We could pick the opposite strategy, and then
       * re-fold into a type abbreviation. But what if the type abbreviation is
       * a TyBar which contains permissions that are only available on one side?
       * That would make the merge operation fail. So let's be conservative and
       * expand eagerly the type abbreviation. *)
      lazy begin
        match is_tyapp left_perm, is_tyapp right_perm with
        | Some (cons1, args1) , _ when is_abbrev left_env cons1 ->
            begin match get_definition left_env cons1 with
            | Some (Abbrev left_perm) ->
                let left_perm = instantiate_type left_perm args1 in
                merge_type_with_unfolding (left_env, left_perm) (right_env, right_perm) ?dest_var dest_env
            | _ ->
                assert false
            end

        | _, Some (cons2, args2) when is_abbrev left_env cons2 ->
            begin match get_definition right_env cons2 with
            | Some (Abbrev right_perm) ->
                let right_perm = instantiate_type right_perm args2 in
                merge_type_with_unfolding (left_env, left_perm) (right_env, right_perm) ?dest_var dest_env
            | _ ->
                assert false
            end

        | _ ->
            None
      end;

    ] in

    MzList.find_opt Lazy.force strategies

  (* end merge_types *)

  (* This just says: if on one side there is a flexible variable, and the other
   * side makes sense in the destination environment, instantiate the flexible
   * variable. *)
  and try_merge_flexible (left_env, left_perm) (right_env, right_perm) dest_env =
    match left_perm, right_perm with
    (* We can instantiate a flexible variable, as long as the type on the other
     * side makes sense in the original environment. *)
    | TyOpen p, t when is_flexible left_env p ->
        begin try
          (* Will raise [UnboundPoint] if we can't get [t] to make sense in
           * the toplevel environment. *)
          let t = clean top right_env t in
          Permissions.instantiate_flexible left_env p t >>= fun left_env ->
          Some (left_env, right_env, dest_env, t)
        with UnboundPoint ->
          None
        end

    | t, TyOpen p when is_flexible right_env p ->
        begin try
          let t = clean top left_env t in
          Permissions.instantiate_flexible right_env p t >>= fun right_env ->
          Some (left_env, right_env, dest_env, t)
        with UnboundPoint ->
          None
        end

    | _ ->
        None

  (* The merge procedure makes the assumption that everything is in the expanded
   * form, that is, that tuples (and concrete types) are of the form
   * "(=x₁, ..., =xₙ)". This assumption is unfortunately broken when entering
   * "opaque" constructs, i.e. those which don't go through the unfolding (see
   * the extended version of the ICFP2013 paper). Right now, we don't merge
   * functions, existentials, universals, or mode constraints (existentials and
   * mode assumptions are removed when performing a [Permissions.add], and we
   * don't use universal values that much). Function types are not merged
   * either. The only "opaque" contexts that remains is type applications and
   * type abbreviations which have not been expanded. For these, we must first
   * unfold the type before performing the merge. *)
  and merge_type_with_unfolding (left_env, left_perm) (right_env, right_perm) ?dest_var dest_env =
    if get_kind_for_type left_env left_perm = KType then
      (* How do we expand a type? We bind a point, and add the permission to the
       * given point. Unfortunately, we don't have an easy way to recover the type
       * we just added to the point, so we use that little hack, telling that when
       * the type is "simple", it remains simple, so we don't have to perform the
       * whole procedure... *)
      let expand env t =
        let t = modulo_flex env t in
        Log.debug "[merge_type_with_unfolding] %a" TypePrinter.ptype (env, t);
        let simple = function TyUnknown | TyDynamic | TySingleton _ -> true | _ -> false in
        if simple t then
          env, t
        else
          let env, point = bind_rigid env (fresh_auto_name "mtwu", KTerm, location env) in
          let env = Permissions.add env point t in
          let t = List.find (fun x -> not (simple x)) (get_permissions env point) in
          env, t
      in
      let left_env, left_perm = expand left_env left_perm in
      let right_env, right_perm = expand right_env right_perm in
      merge_type (left_env, left_perm) (right_env, right_perm) ?dest_var dest_env
    else
      merge_type (left_env, left_perm) (right_env, right_perm) ?dest_var dest_env
  in


  (** This is the start of the actual merge logic. *)

  (* First, start by merging the floating permissions. *)
  let fp_left = get_floating_permissions left_env in
  let fp_right = get_floating_permissions right_env in
  let left_env, unused_fp_left, right_env, unused_fp_right, dest_env, fp_dest =
    merge_lists (left_env, fp_left, []) (right_env, fp_right) (dest_env, [])
  in
  let fp_dest_annot = get_floating_permissions dest_env in
  let dest_env = set_floating_permissions dest_env (fp_dest @ fp_dest_annot) in

  Log.debug ~level:3 "\nInitial floating permissions: %a (extracted with annot: %a)"
    TypePrinter.ptype (top, fold_star (get_floating_permissions top))
    TypePrinter.ptype (dest_env, fold_star fp_dest_annot);
  Log.debug ~level:3 "\nRemaining floating permissions (left): %a"
    TypePrinter.ptype (left_env, fold_star unused_fp_left);
  Log.debug ~level:3 "\nRemaining floating permissions (right): %a"
    TypePrinter.ptype (right_env, fold_star unused_fp_right);
  Log.debug ~level:3 "\nMerged floating permissions: %a\n"
    TypePrinter.ptype (dest_env, fold_star fp_dest);

  (* The main loop. *)
  let state = ref (left_env, right_env, dest_env) in
  while List.length !pending_jobs > 0 do
    (* Get the current merge state. *)
    let left_env, right_env, dest_env = !state in
    (* Next task: merge [left_var] and [right_var] into [dest_var]. *)
    let left_var, right_var, dest_var = pop_job () in
    (* Well, let's do it. *)
    let left_env, right_env, dest_env =
      merge_vars
        (left_env, left_var)
        (right_env, right_var)
        (dest_env, dest_var)
    in
    (* And save it. *)
    state := (left_env, right_env, dest_env);
  done;

  (* Now we're just interested in [dest_env]. *)
  let left_env, right_env, dest_env = !state in

  if false then dump_known_triples left_env right_env dest_env;
  Log.debug ~level:3 "\n--------- END MERGE ----------\n\n%a"
    MzPprint.pdoc (TypePrinter.print_permissions, dest_env);
  Log.debug ~level:3 "\n--------------------------------\n";

  Permissions.safety_check dest_env;

  (* So return it. *)
  (dest_env, dest_root), (!left_conflicts, !right_conflicts, !dest_conflicts)
;;


let merge_envs (top: env) ?(annot: typ option) (left: env * var) (right: env * var): t =
  if is_inconsistent (fst left) then
    right, ([], [], [])
  else if is_inconsistent (fst right) then
    left, ([], [], [])
  else
    actually_merge_envs top ?annot left right
;;
