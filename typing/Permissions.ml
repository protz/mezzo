open Monadic

module Make = functor (M: NDMONAD) -> struct

(* There are useful comments in the corresponding .mli *)

open M

open Types
open Utils

(* -------------------------------------------------------------------------- *)

(* This should help debuggnig. *)

let safety_check env =
  (* Be paranoid, perform an expensive safety check. *)
  Env.fold_terms env (fun () _point _ ({ permissions; _ }) ->
    (* Each term should have exactly one singleton permission. If we fail here,
     * this is SEVERE: this means one of our internal invariants broken, so
     * someone messed up the code somewhere. *)
    let singletons = List.filter (function
      | TySingleton (TyPoint _) ->
          true
      | _ ->
          false
    ) permissions in
    if List.length singletons <> 1 then
      Log.error
        "Inconsistency detected: not one singleton type\n%a\n"
        TypePrinter.penv env;

    (* The inconsistencies below are suspicious, but it may just be that we
     * failed to mark the environment as inconsistent. *)

    (* Unless the environment is inconsistent, a given type should have no
     * more than one concrete type. It may happen that we fail to detect this
     * situation and mark the environment as inconsistent, so this check will
     * explode, and remind us that this is one more situation that will mark an
     * environment as inconsistent. *)
    let concrete = List.filter (function
      | TyConcreteUnfolded _ ->
          true
      | _ ->
          false
    ) permissions in
    if not (env.inconsistent) && List.length concrete > 1 then
      Log.error
        "Inconsistency detected: more than one concrete type\n%a\n"
        TypePrinter.penv env;

    let exclusive = List.filter (FactInference.is_exclusive env) permissions in
    if not (env.inconsistent) && List.length exclusive > 1 then
      Log.error
        "Inconsistency detected: more than one exclusive type\n%a\n"
        TypePrinter.penv env;
  ) ();
;;


(* -------------------------------------------------------------------------- *)

let add_hint hint str =
  match hint with
  | Some (Auto n)
  | Some (User n) ->
      Some (Auto (Variable.register (Variable.print n ^ "_" ^ str)))
  | None ->
      None
;;

(** [can_merge env t1 p2] tells whether, assuming that [t2] is a flexible
    variable, it can be safely merged with [t1]. This function checks that the
    facts are compatible. *)
let can_merge (env: env) (t1: typ) (p2: point): bool =
  Log.check (is_flexible env p2) "[can_merge] takes a flexible variable as its second parameter";
  match t1 with
  | TyPoint p1 ->
      if (is_type env p2) then begin
        Log.check (get_kind env p1 = get_kind env p2) "Wait, what?";
        let f1, f2 = get_fact env p1, get_fact env p2 in
        fact_leq f1 f2
      end else if (is_term env p2) then begin
        (* TODO check for [ghost] here? *)
        true
      end else
        true
  | _ ->
      let f2 = get_fact env p2 in
      let f1 = FactInference.analyze_type env t1 in
      fact_leq f1 f2
;;

(** [collect t] recursively walks down a type with kind TYPE, extracts all
    the permissions that appear into it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    PERM, which represents all the permissions that were just extracted. *)
let collect (t: typ): typ * typ list =
  let rec collect (t: typ): typ * typ list =
    match t with
    | TyUnknown
    | TyDynamic

    | TyVar _
    | TyPoint _

    | TyForall _
    | TyExists _
    | TyApp _

    | TySingleton _

    | TyArrow _ ->
        t, []

    (* Interesting stuff happens for structural types only *)
    | TyBar (t, p) ->
        let t, t_perms = collect t in
        let p, p_perms = collect p in
        t, p :: t_perms @ p_perms

    | TyTuple ts ->
        let ts, permissions = List.split (List.map collect ts) in
        let permissions = List.flatten permissions in
        TyTuple ts, permissions

    | TyConcreteUnfolded (datacon, fields) ->
        let permissions, values = List.partition
          (function FieldPermission _ -> true | FieldValue _ -> false)
          fields
        in
        let permissions = List.map (function
          | FieldPermission p -> p
          | _ -> assert false) permissions
        in
        let sub_permissions, values =
         List.fold_left (fun (collected_perms, reversed_values) ->
            function
              | FieldValue (name, value) ->
                  let value, permissions = collect value in
                  permissions :: collected_perms, (FieldValue (name, value)) :: reversed_values
              | _ ->
                  assert false)
            ([],[])
            values
        in
        TyConcreteUnfolded (datacon, List.rev values), List.flatten (permissions :: sub_permissions)

    | TyAnchoredPermission (x, t) ->
        let t, t_perms = collect t in
        TyAnchoredPermission (x, t), t_perms

    | TyEmpty ->
        TyEmpty, []

    | TyStar (p, q) ->
        let p, p_perms = collect p in
        let q, q_perms = collect q in
        TyStar (p, q), p_perms @ q_perms

    | TyConstraints (constraints, t) ->
        let perms, constraints = List.fold_left (fun (perms, ts) (f, t) ->
          let t, perm = collect t in
          (perm :: perms, (f, t) :: ts)
        ) ([], []) constraints in
        let constraints = List.rev constraints in
        let t, perm = collect t in
        let perms = List.flatten (perm :: perms) in
        TyConstraints (constraints, t), perms
  in
  collect t
;;


(* Collect nested constraints and put them in an outermost position to
 * simplify as much as possible the function type. *)
let rec collect_constraints t =
  match t with
  | TyBar (t, p) ->
      let t, ct = collect_constraints t in
      let p, cp = collect_constraints p in
      TyBar (t, p), ct @ cp
  | TyArrow (t, t') ->
      let t, ct = collect_constraints t in
      TyArrow (t, t'), ct
  | TyStar (p, q) ->
      let p, cp = collect_constraints p in
      let q, cq = collect_constraints q in
      TyStar (p, q), cp @ cq
  | TyTuple ts ->
      let ts, cs = List.split (List.map collect_constraints ts) in
      TyTuple ts, List.flatten cs
  | TyConstraints (cs, t) ->
      let t, cs' = collect_constraints t in
      t, cs @ cs'
  | _ ->
      t, []
;;

let dup_perms_no_singleton env p =
  let perms =
    List.filter (FactInference.is_duplicable env) (get_permissions env p)
  in
  let perms = List.filter (function
    | TySingleton (TyPoint p') when same env p p' ->
        false
    | _ -> true
  ) perms in
  perms
;;


(* -------------------------------------------------------------------------- *)

(* For adding new permissions into the environment. *)

let add_constraints env constraints =
  let env = List.fold_left (fun env (f, t) ->
    let f = fact_of_flag f in
    match t with
    | TyPoint p ->
        let f' = get_fact env p in
        if fact_leq f f' then
        (* [f] tells, for instance, that [p] be exclusive *)
          Env.refresh_fact env p f
        else
          env
    | _ ->
        Log.error "The parser shouldn't allow this"
  ) env constraints in
  env
;;

(** [unify env p1 p2] merges two points, and takes care of dealing with how the
    permissions should be merged. *)
let rec unify (env: env) (p1: point) (p2: point): env mon =
  Log.check (is_term env p1 && is_term env p2) "[unify p1 p2] expects [p1] and \
    [p2] to be variables with kind TERM, not TYPE";

  if same env p1 p2 then
    return env
  else
    (* We need to first merge the environment, otherwise this will go into an
     * infinite loop when hitting the TySingletons... *)
    let perms = get_permissions env p2 in
    let env = merge_left env p1 p2 in
    let () = Log.debug "%a" TypePrinter.penv env in
    foldm (fun env t -> add env p1 t) (return env) perms


(** [add env point t] adds [t] to the list of permissions for [p], performing all
    the necessary legwork. *)
and add (env: env) (point: point) (t: typ): env mon =
  Log.check (is_term env point) "You can only add permissions to a point that \
    represents a program identifier.";

  (* The point is supposed to represent a term, not a type. If it has a
   * structure, this means that it's a type variable with kind TERM that has
   * been flex'd, then instanciated onto something. We make sure in
   * {Permissions.sub} that we're actually merging, not instanciating, when
   * faced with two [TyPoint]s. *)
  Log.check (not (has_structure env point)) "I don't understand what's happening";

  TypePrinter.(Log.debug ~level:4 "[adding to %a] %a"
    pnames (get_names env point)
    ptype (env, t));

  let hint = get_name env point in

  (* We first perform unfolding, so that constructors with one branch are
   * simplified. [unfold] calls [add] recursively whenever it adds new points. *)
  unfold env ~hint t >>= fun (env, t) ->

  (* Break up this into a type + permissions. *)
  let t, perms = collect t in

  (* Add the permissions. *)
  let env = foldm add_perm (return env) perms in
  env >>= fun env ->

  begin match t with
  | TyPoint p when has_structure env p ->
      add env point (Option.extract (structure env p))

  | TySingleton (TyPoint p) when not (same env point p) ->
      unify env point p

  | TyExists (binding, t) ->
      begin match binding with
      | _, KTerm, _ ->
          let env, t = bind_var_in_type env binding t in
          add env point t
      | _ ->
          Log.error "I don't know how to deal with an existentially-quantified \
            type or permission";
      end

  | TyConstraints (constraints, t) ->
      let env = add_constraints env constraints in
      add env point t

  | _ ->
      (* Add the "bare" type. Recursive calls took care of calling [add]. *)
      let env = add_type env point t in
      iter safety_check env;

      env
  end


(** [add_perm env t] adds a type [t] with kind PERM to [env], returning the new
    environment. *)
and add_perm (env: env) (t: typ): env mon =
  TypePrinter.(Log.debug ~level:4 "[add_perm] %a"
    ptype (env, t));

  match t with
  | TyAnchoredPermission (p, t) ->
      add env !!p t
  | TyStar (p, q) ->
      add_perm env p >>= fun env ->
      add_perm env q
  | TyEmpty ->
      return env
  | _ ->
      Log.error "This only works for types with kind PERM."


(* [add_type env p t] adds [t], which is assumed to be unfolded and collected,
 * to the list of available permissions for [p] *)
and add_type (env: env) (p: point) (t: typ): env mon =
  trywith (sub env p t) begin fun env ->
    Log.debug "→ sub worked";
    if FactInference.is_exclusive env t then begin
      (* If [t] is exclusive, then this makes the environment inconsistent. *)
      Log.debug "%sInconsistency detected%s, adding %a as an exclusive \
          permission, but it's already available."
        Bash.colors.Bash.red Bash.colors.Bash.default
        TypePrinter.ptype (env, t);
      return { env with inconsistent = true }
    end else if FactInference.is_duplicable env t then begin
      (* If the type is duplicable, then the [sub] operation didn't perform
       * anything, so we just the environment as-is. *)
      return env
    end else begin
      (* We don't know, be conservative. *)
      return (Env.replace_term env p (fun binding ->
        { binding with permissions = t :: binding.permissions }
      ))
    end
  end begin
    Log.debug "→ sub didn't work";
    return (Env.replace_term env p (fun binding ->
      { binding with permissions = t :: binding.permissions }
    ))
  end


(** [unfold env t] returns [env, t] where [t] has been unfolded, which
    potentially led us into adding new points to [env]. The [hint] serves when
    making up names for intermediary variables. *)
and unfold (env: env) ?(hint: name option) (t: typ): (env * typ) mon =
  (* This auxiliary function takes care of inserting an indirection if needed,
   * that is, a [=foo] type with [foo] being a newly-allocated [point]. *)
  let insert_point (env: env) ?(hint: name option) (t: typ): (env * typ) mon =
    let hint = Option.map_none (Auto (Variable.register (fresh_name "t_"))) hint in
    match t with
    | TySingleton _ ->
        return (env, t)
    | _ ->
        (* The [expr_binder] also serves as the binder for the corresponding
         * TERM type variable. *)
        let env, p = bind_term env hint env.location false in
        (* This will take care of unfolding where necessary. *)
        add env p t >>= fun env ->
        return (env, ty_equals p)
  in

  let rec unfold (env: env) ?(hint: name option) (t: typ): (env * typ) mon =
    match t with
    | TyUnknown
    | TyDynamic
    | TyPoint _
    | TySingleton _
    | TyArrow _
    | TyEmpty ->
        return (env, t)

    | TyVar _ ->
        Log.error "No unbound variables allowed here"

    (* TEMPORARY it's unclear what we should do w.r.t. quantifiers... *)
    | TyForall _
    | TyExists _ ->
        return (env, t)

    | TyStar (p, q) ->
        unfold env ?hint p >>= fun (env, p) ->
        unfold env ?hint q >>= fun (env, q) ->
        return (env, TyStar (p, q))

    | TyBar (t, p) ->
        unfold env ?hint t >>= fun (env, t) ->
        unfold env ?hint p >>= fun (env, p) ->
        return (env, TyBar (t, p))

    | TyAnchoredPermission (x, t) ->
        unfold env ?hint t >>= fun (env, t) ->
        return (env, TyAnchoredPermission (x, t))

    (* If this is the application of a data type that only has one branch, we
     * know how to unfold this. Otherwise, we don't! *)
    | TyApp _ ->
      begin
        let cons, args = flatten_tyapp t in
        match cons with
        | TyPoint p ->
          begin
            match get_definition env p with
            | Some (Some (_, [branch]), _) ->
                let branch = instantiate_branch branch args in
                let t = TyConcreteUnfolded branch in
                unfold env ?hint t
            | _ ->
              return (env, t)
          end
        | _ ->
            Log.error "The head of a type application should be a type variable."
      end

    (* We're only interested in unfolding structural types. *)
    | TyTuple components ->
        Hml_List.fold_lefti (fun i acc component ->
          acc >>= fun (env, components) ->
          let hint = add_hint hint (string_of_int i) in
          insert_point env ?hint component >>= fun (env, component) ->
          return (env, component :: components)
        ) (return (env, [])) components >>= fun (env, components) ->
        return (env, TyTuple (List.rev components))

    | TyConcreteUnfolded (datacon, fields) ->
        foldm (fun (env, fields) -> function
          | FieldPermission _ as field ->
              return (env, field :: fields)
          | FieldValue (name, field) ->
              let hint =
                add_hint hint (Hml_String.bsprintf "%a_%a" Datacon.p datacon Field.p name)
              in
              insert_point env ?hint field >>= fun (env, field) ->
              return (env, FieldValue (name, field) :: fields)
        ) (return (env, [])) fields >>= fun (env, fields) ->
        return (env, TyConcreteUnfolded (datacon, List.rev fields))

    | TyConstraints (constraints, t) ->
        unfold env ?hint t >>= fun (env, t) ->
        return (env, TyConstraints (constraints, t))

  in
  unfold env ?hint t

(** [sub env point t] tries to extract [t] from the available permissions for
    [point] and returns, if successful, the resulting environment. *)
and sub (env: env) (point: point) (t: typ): env mon =
  Log.check (is_term env point) "You can only subtract permissions from a point \
  that represents a program identifier.";

  (* See the explanation in [add]. *)
  Log.check (not (has_structure env point)) "I don't understand what's happening";

  if env.inconsistent then
    return env
  else
    match t with
    | TyUnknown ->
        return env

    | TyDynamic ->
        if begin
          List.exists
            (FactInference.is_exclusive env)
            (get_permissions env point)
        end then
          return env
        else
          fail

    | _ ->

        (* Get a "clean" type without nested permissions. *)
        let t, perms = collect t in
        let perms = List.flatten (List.map flatten_star perms) in

        (* Start off by subtracting the type without associated permissions. *)
        let env = sub_clean env point t in

        env >>= fun env ->
        (* We use a worklist-based approch, where we try to find a permission that
         * "works". A permission that works is one where the left-side is a point
         * that is not flexible, i.e. a point that hopefully should have more to
         * extract than (=itself). As we go, more flexible variables will be
         * unified, which will make more candidates suitable for subtraction. *)
        let works env = function
          | TyAnchoredPermission (TyPoint x, _) when not (is_flexible env x) ->
              return ()
          | _ ->
              fail
        in
        let rec loop = fun (env, worklist) ->
          if List.length worklist > 0 then begin
            take (works env) worklist >>= fun (worklist, (perm, ())) ->
            sub_perm env perm >>= fun env ->
            loop (env, worklist)
          end else
            return env
        in

        loop (env, perms)


(** [sub_clean env point t] takes a "clean" type [t] (without nested permissions)
    and performs the actual work of extracting [t] from the list of permissions
    for [point]. *)
and sub_clean (env: env) (point: point) (t: typ): env mon =
  if (not (is_term env point)) then
    Log.error "[KindCheck] should've checked that for us";
  Log.check (not (has_structure env point)) "Strange";

  let permissions = get_permissions env point in

  (* For when everything's duplicable. *)
  let sort_dup = function
    | TySingleton _ -> 0
    | _ -> 1
  (* For when there's exclusive permissions. *)
  and sort_non_dup = function
    | _ as t when not (FactInference.is_duplicable env t) -> 0
    | TySingleton _ -> 2
    | _ -> 1
  in
  let sort_non_dup x y = sort_non_dup x - sort_non_dup y
  and sort_dup x y = sort_dup x - sort_dup y in
  (* Our heuristic is: if everything's duplicable, [=x] is a suitable type
   * because it's precise and the singleton-subtyping-rule will be able to kick
   * in. Otherwise, because we don't have a linearity analysis on data types, we
   * must be conservative and try to operate on the non-exclusive types. *)
  let is_all_dup = List.for_all (FactInference.is_duplicable env) permissions in
  let permissions =
    List.sort (if is_all_dup then sort_dup else sort_non_dup) permissions
  in

  (* This is a very dumb strategy, that may want further improvements: we just
   * take the first permission that “works”. *)
  let rec traverse (env: env) (seen: typ list) (remaining: typ list): env mon =
    match remaining with
    | hd :: remaining ->
        (* Try to extract [t] from [hd]. *)
        trywith (sub_type env hd t) begin fun env ->
          (* Is this piece of code correct when the singleton-subtyping rule
           * kicks in? Yes, because if we chose to extract [t'] through [=x],
           * [t'] is necessarily duplicable, as is [=x].
           *
           * Is this piece of code optimal? Clearly not, because if [sub_type]
           * encounters [=x], it may go "through" it looking for [x]'s
           * duplicable permissions! This is because [sub_type] doesn't know
           * the context it is called in.
           *
           * [duplicable] has to refer to [hd] since we may do [Nil - list a].
           * [list a] is affine, but that doesn't mean we should take [Nil]
           * out of the list of permissions!
           *)
          let duplicable = FactInference.is_duplicable env hd in

          let open TypePrinter in
          let open Bash in
          let f1 = FactInference.analyze_type env hd in
          let f2 = FactInference.analyze_type env t in
          Log.check
            (fact_leq f1 f2)
            "Fact inconsistency %a <= %a"
            pfact f1
            pfact f2;
          Log.debug ~level:4 "%sTaking%s %a through %a out of the permissions for %a \
            (really? %b)"
            colors.yellow colors.default
            ptype (env, t)
            ptype (env, hd)
            pvar (get_name env point)
            (not duplicable);

          (* We're taking out [hd] from the list of permissions for [point].
           * Is it something duplicable? *)
          if duplicable then
            return env
          else
            return (Env.replace_term env point (fun binder ->
              { binder with permissions = seen @ remaining }))
        end begin
            traverse env (hd :: seen) remaining
        end

    | [] ->
        (* We haven't found any suitable permission. Fail. *)
        fail
  in
  traverse env [] permissions


(** [sub_type env t1 t2] examines [t1] and, if [t1] "provides" [t2], returns
    [Some env] where [env] has been modified accordingly (for instance, by
    unifying some flexible variables); it returns [None] otherwise. *)
and sub_type (env: env) (t1: typ) (t2: typ): env mon =
  TypePrinter.(
    Log.debug ~level:4 "[sub_type] %a %s→%s %a"
      ptype (env, t1)
      Bash.colors.Bash.red Bash.colors.Bash.default
      ptype (env, t2));

  if equal env t1 t2 then
    return env
  else match t1, t2 with
  | _, TyUnknown ->
      return env

  | TyConstraints _, _ ->
      Log.error "Constraints should've been processed when this permission was added"

  | _, TyConstraints (constraints, t2) ->
      foldm (fun env (f, t) ->
        let f = fact_of_flag f in
        match t with
        | TyPoint p ->
            let f' = get_fact env p in
            (* [f] demands, for instance, that [p] be exclusive *)
            if fact_leq f' f then
              return env
            else
              fail
        | _ ->
            Log.error "The parser shouldn't allow this"
      ) (return env) constraints >>= fun env ->
      sub_type env t1 t2


  | TyForall (binding, t1), _ ->
      let env, t1 = bind_var_in_type ~flexible:true env binding t1 in
      sub_type env t1 t2

  | _, TyForall (binding, t2) ->
      (* Typical use-case: Nil vs [a] list a. We're binding this as a *rigid*
       * type variable. *)
      let env, t2 = bind_var_in_type env binding t2 in
      sub_type env t1 t2

  | TyExists (binding, t1), _ ->
      let env, t1 = bind_var_in_type env binding t1 in
      (* TODO collect permissions inside [t1] and add them to the environment!
       * We should probably do something similar for the two cases above
       * although I'm not sure I understand what should happen... *)
      sub_type env t1 t2

  | _, TyExists (binding, t2) ->
      let env, t2 = bind_var_in_type ~flexible:true env binding t2 in
      let t2, perms = collect t2 in
      foldm
        sub_perm
        (sub_type env t1 t2)
        perms

  | TyTuple components1, TyTuple components2 ->
      (* We can only subtract a tuple from another one if they have the same
       * length. *)
      if List.length components1 <> List.length components2 then
        fail

      (* We assume here that the [t1] is in expanded form, that is, that [t1] is
       * only a tuple of singletons. *)
      else
        List.fold_left2 (fun env c1 c2 ->
          env >>= fun env ->
          match c1 with
          | TySingleton (TyPoint p) ->
              sub_clean env p c2
          | _ ->
              Log.error "All permissions should be in expanded form."
        ) (return env) components1 components2

  | TyConcreteUnfolded (datacon1, fields1), TyConcreteUnfolded (datacon2, fields2) ->
      if Datacon.equal datacon1 datacon2 then
        List.fold_left2 (fun env f1 f2 ->
          env >>= fun env ->
          match f1 with
          | FieldValue (name1, TySingleton (TyPoint p)) ->
              begin match f2 with
              | FieldValue (name2, t) ->
                  Log.check (Field.equal name1 name2) "Not in order?";
                  sub_clean env p t
              | _ ->
                  Log.error "The type we're trying to extract should've been \
                    cleaned first."
              end
          | _ ->
              Log.error "All permissions should be in expanded form."
        ) (return env) fields1 fields2

      else
        fail

  | TyConcreteUnfolded (datacon1, _), TyApp _ ->
      let cons2, args2 = flatten_tyapp t2 in
      let point1 = DataconMap.find datacon1 env.type_for_datacon in

      if same env point1 !!cons2 then begin
        let branch2 = find_and_instantiate_branch env !!cons2 datacon1 args2 in
        sub_type env t1 (TyConcreteUnfolded branch2)
      end else begin
        fail
      end

  | TyConcreteUnfolded (datacon1, _), TyPoint point2 when not (is_flexible env point2) ->
      (* The case where [point2] is flexible is taken into account further down,
       * as we may need to perform a unification. *)
      let point1 = DataconMap.find datacon1 env.type_for_datacon in

      if same env point1 point2 then begin
        let branch2 = find_and_instantiate_branch env point2 datacon1 [] in
        sub_type env t1 (TyConcreteUnfolded branch2)
      end else begin
        fail
      end

  | TyApp _, TyApp _ ->
      let cons1, args1 = flatten_tyapp t1 in
      let cons2, args2 = flatten_tyapp t2 in

      if same env !!cons1 !!cons2 then
        Hml_List.fold_left2i (fun i env arg1 arg2 ->
          env >>= fun env ->
          (* Variance comes into play here as well. The behavior is fairly
           * intuitive. *)
          match variance env !!cons1 i with
          | Covariant ->
              sub_type env arg1 arg2
          | Contravariant ->
              sub_type env arg2 arg1
          | Bivariant ->
              return env
          | Invariant ->
              equal_modulo_flex env arg1 arg2
        ) (return env) args1 args2
      else
        fail

  | TySingleton t1, TySingleton t2 ->
      sub_type env t1 t2

  | TyArrow (t1, t2), TyArrow (t'1, t'2) ->
      sub_type env t1 t'1 >>= fun env ->
      sub_type env t'2 t2

  | TyBar (t1, p1), TyBar (t2, p2) ->
      sub_type env t1 t2 >>= fun env ->
      add_perm env p1 >>= fun env ->
      sub_perm env p2

  (* This is the singleton-subtyping rule. *)
  | TySingleton (TyPoint p), _ when FactInference.is_duplicable env t2 ->
      dispatch
        (fun t1 -> sub_type env t1 t2)
        (dup_perms_no_singleton env p)

  | _ ->
      compare_modulo_flex env sub_type t1 t2


and try_merge_flex env p t =
  if is_flexible env p && can_merge env t p then
    return (instantiate_flexible env p t)
  else
    fail


and try_merge_point_to_point env p1 p2 =
  if is_flexible env p2 then
    return (merge_left env p1 p2)
  else
    fail

and compare_modulo_flex env k t1 t2 =
  let c = compare_modulo_flex in
  match t1, t2 with
  | TyPoint p1, TyPoint p2 ->
      if same env p1 p2 then
        return env
      else
        try_merge_point_to_point env p1 p2 |||
        try_merge_point_to_point env p2 p1 |||
        (structure env p1 >>?= fun t1 -> c env k t1 t2) |||
        (structure env p2 >>?= fun t2 -> c env k t1 t2)

  | TyPoint p1, _ ->
      try_merge_flex env p1 t2 |||
      (structure env p1 >>?= fun t1 -> c env k t1 t2)

  | _, TyPoint p2 ->
      try_merge_flex env p2 t1 |||
      (structure env p2 >>?= fun t2 -> c env k t1 t2)

  | _ ->
      if equal env t1 t2 then
        return env
      else
        fail

and equal_modulo_flex env t1 t2 =
  compare_modulo_flex env equal_modulo_flex t1 t2

(** [sub_perm env t] takes a type [t] with kind PERM, and tries to return the
    environment without the corresponding permission. *)
and sub_perm (env: env) (t: typ): env mon =
  TypePrinter.(
    Log.debug ~level:4 "[sub_perm] %a"
      ptype (env, t));

  match t with
  | TyAnchoredPermission (TyPoint p, t) ->
      sub env p t
  | TyStar (p, q) ->
      sub_perm env p >>= fun env ->
      sub_perm env q
  | TyEmpty ->
      return env
  | _ ->
      Log.error "[sub_perm] the following type does not have kind PERM: %a (%a)"
        TypePrinter.ptype (env, t)
        Utils.ptag t
;;


(* -------------------------------------------------------------------------- *)

(* For pretty-printing. *)

exception NotFoldable

(** [fold env point] tries to find (hopefully) one "main" type for [point], by
    folding back its "main" type [t] into a form that's suitable for one
    thing, and one thing only: printing. *)
let rec fold (env: env) (point: point): typ option =
  let perms = get_permissions env point in
  let perms = List.filter
    (function
      | TySingleton (TyPoint p) when same env p point ->
          false
      | _ ->
          true
    ) perms
  in
  match perms with
  | [] ->
      Some TyUnknown
  | t :: [] ->
      begin try
        Some (fold_type_raw env t)
      with NotFoldable ->
        None
      end
  | _ ->
      None


and fold_type_raw (env: env) (t: typ): typ =
  match t with
  | TyUnknown
  | TyDynamic ->
      t

  | TyVar _ ->
      Log.error "All types should've been opened at that stage"

  | TyPoint _ ->
      t

  | TyForall _
  | TyExists _
  | TyApp _ ->
      t

  | TySingleton (TyPoint p) ->
      begin match fold env p with
      | Some t ->
          t
      | None ->
          raise NotFoldable
      end

  | TyTuple components ->
      TyTuple (List.map (fold_type_raw env) components)

  | TyConstraints (cs, t) ->
      TyConstraints (cs, fold_type_raw env t)

  (* TODO *)
  | TyConcreteUnfolded _ ->
      t

  | TySingleton _ ->
      t

  | TyArrow _ ->
      t

  | TyBar (t, p) ->
      TyBar (fold_type_raw env t, p)

  | TyAnchoredPermission (x, t) ->
      TyAnchoredPermission (x, fold_type_raw env t)

  | TyEmpty ->
      t

  | TyStar _ ->
      Log.error "Huh I don't think we should have that here"

;;

let fold_type env t =
  try
    Some (fold_type_raw env t)
  with NotFoldable ->
    None
;;

end (* end functor *)
