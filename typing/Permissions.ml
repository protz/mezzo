(* There are useful comments in the corresponding .mli *)

open Types
open Utils

(* Saves us the trouble of matching all the time. *)
let (!!) = function TyPoint x -> x | _ -> assert false;;

type refined_type = Both | One of typ

exception Inconsistent

(** [can_merge env t1 p2] tells whether, assuming that [t2] is a flexible
    variable, it can be safely merged with [t1]. This function checks that the
    facts are compatible. *)
let can_merge (env: env) (t1: typ) (p2: point): bool =
  match t1 with
  | TyPoint p1 ->
      Log.affirm (is_flexible env p2) "[can_merge] takes a flexible variable \
        as its second parameter";
      Log.affirm (get_kind env p1 = get_kind env p2) "Wait, what?";
      let f1, f2 = get_fact env p1, get_fact env p2 in
      fact_leq f1 f2
  | _ ->
      Log.affirm (is_flexible env p2) "[can_merge] takes a flexible variable \
        as its second parameter";
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

    (* Interesting stuff happens for strctural types only *)
    | TyTuple components ->
        let permissions, values = List.partition
          (function TyTupleComponentPermission _ -> true | TyTupleComponentValue _ -> false)
          components
        in
        let permissions = List.map (function
          | TyTupleComponentPermission p -> p
          | _ -> assert false) permissions
        in
        let sub_permissions, values =
          List.fold_left (fun (collected_perms, reversed_values) ->
            function
              | TyTupleComponentValue value ->
                  let value, permissions = collect value in
                  permissions :: collected_perms, (TyTupleComponentValue value) :: reversed_values
              | _ ->
                  assert false)
            ([],[])
            values
        in
        let t =
          if List.length values = 1 then
            match List.nth values 0 with
              | TyTupleComponentValue v -> v
              | _ -> assert false
          else
            TyTuple (List.rev values)
        in
        t, List.flatten (permissions :: sub_permissions)

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

    | TyAnchoredPermission _
    | TyEmpty
    | TyStar _ ->
        Log.error "This function takes a [type] with kind [TYPE]."
  in
  collect t
;;

(** [unfold env t] returns [env, t] where [t] has been unfolded, which
    potentially led us into adding new points to [env]. The [hint] serves when
    making up names for intermediary variables. *)
let rec unfold (env: env) ?(hint: string option) (t: typ): env * typ =
  (* This auxiliary function takes care of inserting an indirection if needed,
   * that is, a [=foo] type with [foo] being a newly-allocated [point]. *)
  let insert_point (env: env) ?(hint: string option) (t: typ): env * typ =
    let hint = Option.map_none (fresh_name "t_") hint in
    match t with
    | TySingleton _ ->
        env, t
    | _ ->
        (* The [expr_binder] also serves as the binder for the corresponding
         * TERM type variable. *)
        let env, p = bind_term env (Variable.register hint) false in
        (* This will take care of unfolding where necessary. *)
        let env = add env p t in
        env, TySingleton (TyPoint p)
  in

  let rec unfold (env: env) ?(hint: string option) (t: typ): env * typ =
    match t with
    | TyUnknown
    | TyDynamic
    | TyPoint _
    | TySingleton _
    | TyArrow _
    | TyEmpty ->
        env, t

    | TyVar _ ->
        Log.error "No unbound variables allowed here"

    (* TEMPORARY it's unclear what we should do w.r.t. quantifiers... *)
    | TyForall _
    | TyExists _ ->
        env, t

    | TyStar (p, q) ->
        let env, p = unfold env ?hint p in
        let env, q = unfold env ?hint q in
        env, TyStar (p, q)

    | TyAnchoredPermission (x, t) ->
        let env, t = unfold env ?hint t in
        env, TyAnchoredPermission (x, t)

    (* If this is the application of a data type that only has one branch, we
     * know how to unfold this. Otherwise, we don't! *)
    | TyApp _ ->
      begin
        let cons, args = flatten_tyapp t in
        match cons with
        | TyPoint p ->
          begin
            match get_definition env p with
            | Some (_, [branch]) ->
                let branch = instantiate_branch branch args in
                let t = TyConcreteUnfolded branch in
                unfold env ?hint t
            | _ ->
              env, t
          end
        | _ ->
            Log.error "The head of a type application should be a type variable."
      end

    (* We're only interested in unfolding structural types. *)
    | TyTuple components ->
        let env, components = Hml_List.fold_lefti (fun i (env, components) -> function
          | TyTupleComponentPermission _ as component ->
              env, component :: components
          | TyTupleComponentValue component ->
              let hint = Option.map (fun hint -> Printf.sprintf "%s_%d" hint i) hint in
              let env, component = insert_point env ?hint component in
              env, TyTupleComponentValue component :: components
        ) (env, []) components in
        env, TyTuple (List.rev components)

    | TyConcreteUnfolded (datacon, fields) ->
        let env, fields = List.fold_left (fun (env, fields) -> function
          | FieldPermission _ as field ->
              env, field :: fields
          | FieldValue (name, field) ->
              let hint = Option.map (fun hint ->
                Hml_String.bsprintf "%s_%a_%a" hint Datacon.p datacon Field.p name
              ) hint in
              let env, field = insert_point env ?hint field in
              env, FieldValue (name, field) :: fields
        ) (env, []) fields
        in
        env, TyConcreteUnfolded (datacon, List.rev fields)

  in
  unfold env ?hint t


(** [refine_type env t1 t2] tries, given [t1], to turn it into something more
    precise using [t2]. It returns [Both] if both types are to be kept, or [One
    t3] if [t1] and [t2] can be combined into a more precise [t3].

    The order of the arguments does not matter: [refine_type env t1 t2] is equal
    to [refine_type env t2 t1]. *)
and refine_type (env: env) (t1: typ) (t2: typ): env * refined_type =
  (* TEMPORARY find a better name for that function; what it means is « someone else can view this
   * type » *)
  let views t =
    match t with
    | TyApp _ ->
        let cons, _ = flatten_tyapp t in
        has_definition env !!cons
    | TyConcreteUnfolded _
    | TyArrow _
    | TyTuple _ ->
        true
    | _ ->
        false
  in

  let f1 = FactInference.analyze_type env t1 in
  let f2 = FactInference.analyze_type env t2 in

  (* Small wrapper that makes sure we only return one permission if the two
   * original ones were duplicable. *)
  let one_if t =
    if f1 = Duplicable [||] then begin
      Log.affirm (f1 = f2) "Two equal types should have equal facts";
      One t
    end else
      Both
  in

  TypePrinter.(
    Log.debug ~level:4 "Refinement: %a, %a" pfact f1 pfact f2
  );

  try

    (* Having two exclusive permissions on the same point means we're duplicating an *exclusive*
     * access right to the heap. *)
    if f1 = Exclusive && f2 = Exclusive then
      raise Inconsistent;

    (* Exclusive means we're the only one « seeing » this type; if someone else can see the type,
     * we're inconsistent too. Having [t1] exclusive and [t2 = TyAbstract] is not a problem: [t2]
     * could be a hidden [TyDynamic], for instance. *)
    if f1 = Exclusive && views t2 || f2 = Exclusive && views t1 then
      raise Inconsistent;

    match t1, t2 with
    | TyApp _, TyApp _ ->
        (* Type applications. This covers the following cases:
           - abstract vs abstract
           - concrete vs concrete (NOT unfolded)
           - concrete vs abstract *)
        let cons1, args1 = flatten_tyapp t1 in
        let cons2, args2 = flatten_tyapp t2 in

        if same env !!cons1 !!cons2 && List.for_all2 (equal env) args1 args2 then
          env, one_if t1
        else
          env, Both

    | TyConcreteUnfolded branch as t, other
    | other, (TyConcreteUnfolded branch as t) ->
        (* Unfolded concrete types. This covers:
           - unfolded vs unfolded,
           - unfolded vs nominal. *)
        begin match other with
        | TyConcreteUnfolded branch' ->
            (* Unfolded vs unfolded *)
            let datacon, fields = branch in
            let datacon', fields' = branch' in

            if Datacon.equal datacon datacon' then
              (* The names are equal. Both types are unfolded, so recursively unify their fields. *)
              let env = List.fold_left2 (fun env f1 f2 ->
                match f1, f2 with
                | FieldValue (name1, t1), FieldValue (name2, t2) ->
                    Log.affirm (Field.equal name1 name2)
                      "Fields are not in the same order, I thought they were";

                    (* [unify] is responsible for performing the entire job. *)
                    begin match t1, t2 with
                    | TySingleton (TyPoint p1), TySingleton (TyPoint p2) ->
                        unify env p1 p2
                    | _ ->
                        Log.error "The type should've been run through [unfold] before"
                    end

                | _ ->
                    Log.error "The type should've been run through [collect] before"
              ) env fields fields' in
              env, One t1

            else
              raise Inconsistent

        | TyApp _ ->
            (* Unfolded vs nominal, we transform this into unfolded vs unfolded. *)
            let cons, args = flatten_tyapp other in
            let datacon, _ = branch in

            if same env (DataconMap.find datacon env.type_for_datacon) !!cons then
              let branch' = find_and_instantiate_branch env !!cons datacon args in
              let env, t' = unfold env (TyConcreteUnfolded branch') in
              refine_type env t t'
            else
              (* This is fairly imprecise as well. If both types are concrete
               * *and* different, this is inconsistent. However, if [other] is
               * the applicatino of an abstract data type, then of course it is
               * not inconsistent. *)
              env, Both

        | _ ->
            (* This is fairly imprecise. [TyConcreteUnfolded] vs [TyForall] is
             * of course inconsistent, but [TyConcreteUnfolded] vs [TyPoint]
             * where [TyPoint] is an abstract type is not inconsistent. However,
             * if the [TyPoint] is [int], it definitely is inconsistent. But we
             * have no way to distinguish "base types" and abstract types... *)
            env, Both

        end

    | TyTuple components1, TyTuple components2 ->
        if List.(length components1 <> length components2) then
          raise Inconsistent

        else
          let env = List.fold_left2 (fun env c1 c2 ->
            match c1, c2 with
            | TyTupleComponentValue t1, TyTupleComponentValue t2 ->
                (* [unify] is responsible for performing the entire job. *)
                begin match t1, t2 with
                | TySingleton (TyPoint p1), TySingleton (TyPoint p2) ->
                    unify env p1 p2
                | _ ->
                    Log.error "The type should've been run through [unfold] before"
                end

            | _ ->
                Log.error "The type should've been run through [collect] before"
          ) env components1 components2 in
          env, One t1

    | TyForall _, _
    | _, TyForall _
    | TyExists _, _
    | _, TyExists _ ->
        (* We don't know how to refine in the presence of quantifiers. We should
         * probably think about it hard and do something very fancy. *)
        env, Both

    | TyAnchoredPermission _, _
    | _, TyAnchoredPermission _
    | TyEmpty, _
    | _, TyEmpty
    | TyStar _, _
    | _, TyStar _ ->
        Log.error "We can only refine types that have kind TYPE."

    | TyUnknown, (_ as t)
    | (_ as t), TyUnknown ->
        env, One t

    | (_ as t), TyPoint p
    | TyPoint p, (_ as t) ->
        begin match structure env p with
        | Some t' ->
            refine_type env t t'
        | None ->
            env, Both
        end

    | _ ->
        (* TEMPORARY this seems overly aggressive and expensive *)
        if equal env t1 t2 then
          env, one_if t1
        else
          (* If there's nothing we can say, keep both. *)
          env, Both

  with Inconsistent ->

    (* XXX our inconsistency analysis is sub-optimal, see various comments
     * above. *)
    let open TypePrinter in
    Log.debug ~level:4 "Inconsistency detected %a cannot coexist with %a"
      pdoc (ptype, (env, t1)) pdoc (ptype, (env, t2));

    (* We could possibly be smarter here, and mark the entire permission soup as
     * being inconsistent. This would allow us to implement some sort of
     * [absurd] construct that asserts that the program point is not reachable. *)
    env, Both


(** [refine env p t] adds [t] to the list of available permissions for [p],
    possibly by refining some of these permissions into more precise ones. *)
and refine (env: env) (point: point) (t': typ): env =
  let permissions = get_permissions env point in
  let rec refine_list (env, acc) t' = function
    | t :: ts ->
        let env, r = refine_type env t t' in
        begin match r with
        | Both ->
            refine_list (env, (t :: acc)) t' ts
        | One t' ->
            refine_list (env, acc) t' ts
        end
    | [] ->
        env, t' :: acc
  in
  let env, permissions = refine_list (env, []) t' permissions in
  replace_term env point (fun binder -> { binder with permissions })


(** [unify env p1 p2] merges two points, and takes care of dealing with how the
    permissions should be merged. *)
and unify (env: env) (p1: point) (p2: point): env =
  Log.affirm (is_term env p1 && is_term env p2) "[unify p1 p2] expects [p1] and \
    [p2] to be variables with kind TERM, not TYPE";

  if same env p1 p2 then
    env
  else
    let env =
      List.fold_left (fun env t -> refine env p1 t) env (get_permissions env p2)
    in
    merge_left env p1 p2


(** [add env point t] adds [t] to the list of permissions for [p], performing all
    the necessary legwork. *)
and add (env: env) (point: point) (t: typ): env =
  Log.affirm (is_term env point) "You can only add permissions to a point that \
    represents a program identifier.";

  let hint = Variable.print (get_name env point) in

  (* We first perform unfolding, so that constructors with one branch are
   * simplified. *)
  let env, t = unfold env ~hint t in

  (* Now we may have more opportunities for collecting permissions. [collect]
   * doesn't go "through" [TyPoint]s but when indirections are inserted via
   * [insert_point], [add] is recursively called, so inner permissions are
   * collected as well. *)
  let t, perms = collect t in
  let env = List.fold_left add_perm env perms in
  refine env point t


(** [add_perm env t] adds a type [t] with kind PERM to [env], returning the new
    environment. *)
and add_perm (env: env) (t: typ): env =
  match t with
  | TyAnchoredPermission (TyPoint p, t) ->
      add env p t
  | TyStar (p, q) ->
      add_perm (add_perm env p) q
  | TyEmpty ->
      env
  | _ ->
      Log.error "[add_perm] only works with types that have kind PERM"
;;


(** [sub env point t] tries to extract [t] from the available permissions for
    [point] and returns, if successful, the resulting environment. *)
let rec sub (env: env) (point: point) (t: typ): env option =
  Log.affirm (is_term env point) "You can only add permissions to a point that \
    represents a program identifier.";

  match t with
  | TyUnknown ->
      Some env

  | TyDynamic ->
      if begin
        List.exists
          (fun t -> FactInference.analyze_type env t = Exclusive)
          (get_permissions env point)
      end then
        Some env
      else
        None

  | _ ->

      (* Get a "clean" type without nested permissions. *)
      let t, perms = collect t in

      (* TEMPORARY we should probably switch to a more sophisticated strategy,
       * based on a work list. The code would scan the work list for a permission
       * that it knows how to extract. A failure would happen when there are
       * permissions left but we don't know how to extract them because the
       * variables are still flexible, for instance... *)
      let env = sub_clean env point t in
      List.fold_left
        (fun env perm -> (Option.bind env (fun env -> sub_perm env perm)))
        env
        perms


(** [sub_clean env point t] takes a "clean" type [t] (without nested permissions)
    and performs the actual work of extracting [t] from the list of permissions
    for [point]. *)
and sub_clean (env: env) (point: point) (t: typ): env option =
  let permissions = get_permissions env point in

  (* This is a very dumb strategy, that may want further improvements: we just
   * take the first permission that “works”. *)
  let rec traverse (env: env) (seen: typ list) (remaining: typ list): env option =
    match remaining with
    | hd :: remaining ->
        (* Try to extract [t] from [hd]. *)
        begin match sub_type env hd t with
        | Some env ->
            TypePrinter.(
              Log.debug ~level:4 "Taking %a out of the permissions for %a"
                pdoc (ptype, (env, hd)) Variable.p (get_name env point));
            (* We're taking out [hd] from the list of permissions for [point].
             * Is it something duplicable? *)
            let fact = FactInference.analyze_type env hd in
            if fact = Duplicable [||] then
              Some env
            else
              Some (replace_term env point (fun binder ->
                { binder with permissions = seen @ remaining }))
        | None ->
            traverse env (hd :: seen) remaining
        end

    | [] ->
        (* We haven't found any suitable permission. Fail. *)
        None
  in
  traverse env [] permissions


(** [sub_type env t1 t2] examines [t1] and, if [t1] "provides" [t2], returns
    [Some env] where [env] has been modified accordingly (for instance, by
    unifying some flexible variables); it returns [None] otherwise. *)
and sub_type (env: env) (t1: typ) (t2: typ): env option =
  TypePrinter.(
    Log.debug ~level:4 "sub_type\n  t1 %a\n  t2 %a"
      pdoc (ptype, (env, t1))
      pdoc (ptype, (env, t2)));
  match t1, t2 with
  | TyTuple components1, TyTuple components2 ->
      (* We can only substract a tuple from another one if they have the same
       * length. *)
      if List.length components1 <> List.length components2 then
        None

      (* We assume here that the [t1] is in expanded form, that is, that [t1] is
       * only a tuple of singletons. *)
      else
        List.fold_left2 (fun env c1 c2 ->
          Option.bind env (fun env ->
            match c1 with
            | TyTupleComponentValue (TySingleton (TyPoint p)) ->
                begin match c2 with
                | TyTupleComponentValue t ->
                    sub_clean env p t
                | _ ->
                    Log.error "The type we're trying to extract should've been \
                      cleaned first."
                end
            | _ ->
                Log.error "All permissions should be in expanded form."
          )
        ) (Some env) components1 components2

  | TyConcreteUnfolded (datacon1, fields1), TyConcreteUnfolded (datacon2, fields2) ->
      if Datacon.equal datacon1 datacon2 then
        List.fold_left2 (fun env f1 f2 ->
          Option.bind env (fun env ->
            match f1 with
            | FieldValue (name1, TySingleton (TyPoint p)) ->
                begin match f2 with
                | FieldValue (name2, t) ->
                    Log.affirm (Field.equal name1 name2) "Not in order?";
                    sub_clean env p t
                | _ ->
                    Log.error "The type we're trying to extract should've been \
                      cleaned first."
                end
            | _ ->
                Log.error "All permissions should be in expanded form."
          )
        ) (Some env) fields1 fields2

      else
        None

  | TyConcreteUnfolded (datacon1, _), TyApp _ ->
      let cons2, args2 = flatten_tyapp t2 in
      let point1 = DataconMap.find datacon1 env.type_for_datacon in

      if same env point1 !!cons2 then begin
        let branch2 = find_and_instantiate_branch env !!cons2 datacon1 args2 in
        sub_type env t1 (TyConcreteUnfolded branch2)
      end else begin
        None
      end

  | TyConcreteUnfolded (datacon1, _), TyPoint point2 ->
      let point1 = DataconMap.find datacon1 env.type_for_datacon in

      if same env point1 point2 then begin
        let branch2 = find_and_instantiate_branch env point2 datacon1 [] in
        sub_type env t1 (TyConcreteUnfolded branch2)
      end else begin
        None
      end


  | TyApp _, TyApp _ ->
      let cons1, args1 = flatten_tyapp t1 in
      let cons2, args2 = flatten_tyapp t2 in

      if same env !!cons1 !!cons2 then
        List.fold_left2
          (fun env arg1 arg2 -> Option.bind env (fun env -> sub_type env arg1 arg2))
          (Some env) args1 args2
      else
        None

  | TyPoint p1, TyPoint p2 ->
      if same env p1 p2 then
        Some env
      else if is_flexible env p2 && can_merge env t1 p2 then
        Some (merge_left env p1 p2)
      else
        None

  | _, TyPoint p2 ->
      if is_flexible env p2 then
          if can_merge env t1 p2 then
            Some (instantiate_flexible env p2 t1)
          else
            None
      else
        begin match structure env p2 with
        | Some t2 ->
            sub_type env t1 t2
        | None ->
            None
        end

  | _ ->
      if equal env t1 t2 then
        Some env
      else
        None


(** [sub_perm env t] takes a type [t] with kind PERM, and tries to return the
    environment without the corresponding permission. *)
and sub_perm (env: env) (t: typ): env option =
  match t with
  | TyAnchoredPermission (TyPoint p, t) ->
      sub env p t
  | TyStar (p, q) ->
      Option.bind
        (sub_perm env p)
        (fun env -> sub_perm env q)
  | TyEmpty ->
      Some env
  | _ ->
      Log.error "[sub_perm] only works with types that have kind PERM"
;;


let full_merge (env: env) (p: point) (p': point): env =
  Log.affirm (is_term env p && is_term env p') "Only interested in TERMs here.";

  let perms = get_permissions env p' in
  let env = merge_left env p p' in
  List.fold_left (fun env t -> add env p t) env perms
;;
