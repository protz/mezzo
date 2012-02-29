(** This module provides permission manipulation functions. *)

open Types

let fresh_name prefix =
  let counter = ref 0 in
  let n = string_of_int !counter in
  counter := !counter + 1;
  prefix ^ n
;;

type refined_type = Both | One of typ

exception Inconsistent

(* [unfold env t] returns [env, t] where [t] has been unfolded, which
 * potentially led us into adding new points to [env]. *)
let rec unfold (env: env) ?(hint: string option) (t: typ): env * typ =

  (* This auxiliary function takes care of inserting an indirection if needed,
   * that is, a [=foo] type with [foo] being a newly-allocated [point]. *)
  let rec insert_point (env: env) (hint: string) (t: typ): env * typ =
    match t with
    | TySingleton _ ->
        env, t
    | _ ->
        (* The [expr_binder] also serves as the binder for the corresponding
         * TERM type variable. *)
        let env, p = bind_expr env (Variable.register hint) in
        (* This will take care of unfolding where necessary. *)
        let env = add env p t in
        env, TySingleton (TyPoint p)

  and unfold (env: env) ?(hint: string option) (t: typ): env * typ =
    let hint = Option.map_none (fresh_name "t_") hint in
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
        let env, p = unfold env ~hint p in
        let env, q = unfold env ~hint q in
        env, TyStar (p, q)

    | TyAnchoredPermission (x, t) ->
        let env, t = unfold env ~hint t in
        env, TyAnchoredPermission (x, t)

    (* If this is the application of a data type that only has one branch, we
     * know how to unfold this. Otherwise, we don't! *)
    | TyApp _ ->
      begin
        let cons, args = flatten_tyapp t in
        match cons with
        | TyPoint p ->
          begin
            match branches_for_type env p with
            | Some [branch] ->
                let branch = instantiate_branch branch args in
                let t = TyConcreteUnfolded branch in
                unfold env ~hint t
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
              let hint = Printf.sprintf "%s_%d" hint i in
              let env, component = insert_point env hint component in
              env, TyTupleComponentValue component :: components
        ) (env, []) components in
        env, TyTuple (List.rev components)

    | TyConcreteUnfolded (datacon, fields) ->
        let env, fields = List.fold_left (fun (env, fields) -> function
          | FieldPermission _ as field ->
              env, field :: fields
          | FieldValue (name, field) ->
              let hint =
                Hml_String.bsprintf "%s_%a_%a" hint Datacon.p datacon Field.p name
              in
              let env, field = insert_point env hint field in
              env, FieldValue (name, field) :: fields
        ) (env, []) fields
        in
        env, TyConcreteUnfolded (datacon, List.rev fields)

  in
  unfold env ?hint t

(* [refine_type env t1 t2] tries, given [t1], to turn it into something more
 * precise using [t2]. It returns [Both] if both types are to be kept, or [One
 * t3] if [t1] and [t2] can be combined into a more precise [t3]. *)
and refine_type (env: env) (t1: typ) (t2: typ): env * refined_type =
  (* Save us the trouble of matching all the time. *)
  let (!!) = function TyPoint x -> x | _ -> assert false in

  (* TEMPORARY find a better name for that function; what it means is « someone else can view this
   * type » *)
  let views t =
    match t with
    | TyApp _ ->
        let cons, _ = flatten_tyapp t in
        is_concrete env !!cons
    | TyConcreteUnfolded _
    | TyArrow _
    | TyTuple _ ->
        true
    | _ ->
        false
  in

  let f1 = FactInference.analyze_type env t1 in
  let f2 = FactInference.analyze_type env t2 in
  TypePrinter.(
    Log.debug ~level:4 "Refinement: %a, %a" pdoc (do_print_fact, f1) pdoc (do_print_fact, f2)
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

        begin match def_for_type env !!cons1, def_for_type env !!cons2 with
        | Concrete _, Concrete _ ->
            if same env !!cons1 !!cons2 then
              if List.for_all2 (equal env) args1 args2 then
                (* Small optimisation: if the arguments are equal, just keep one
                 * of the two. *)
                env, One t1
              else
                (* Nothing we can say about the arguments here. This could very
                 * well be a data type that does not use its arguments. *)
                env, Both
            else
              raise Inconsistent

        | Abstract _, _
        | _, Abstract _ ->
            if same env !!cons1 !!cons2 && List.for_all2 (equal env) args1 args2 then
              env, One t1
            else
              (* There's nothing we can say here. The [Abstract] could hide anything, even [TyUnknown]. *)
              env, Both

        | _ ->
            Log.error "Huh? Flexible?"
        end

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
                    (* I don't think this should raise en error, but to be on the safe side, we
                     * could sort fields beforehand. *)
                    if not (Field.equal name1 name2) then
                      Log.error "Fields are not in the same order, FIXME";

                    (* [unify] is responsible for performing the entire job. *)
                    begin match t1, t2 with
                    | TySingleton (TyPoint p1), TySingleton (TyPoint p2) ->
                        unify env p1 p2
                    | _ ->
                        Log.error "Not supported"
                    end

                | _ ->
                    Log.error "Not supported"
              ) env fields fields' in
              env, One t1

            else
              raise Inconsistent

        | TyApp _ ->
            (* Unfolded vs nominal, we transform this into unfolded vs unfolded. *)
            let cons, args = flatten_tyapp other in
            let datacon, _ = branch in

            if same env (DataconMap.find datacon env.type_for_datacon) !!cons then
              let branches' = Option.extract (branches_for_type env !!cons) in
              let branch' =
                List.find
                  (fun (datacon', _) -> Datacon.equal datacon datacon')
                  branches'
              in
              let branch' = instantiate_branch branch' args in
              let env, t' = unfold env (TyConcreteUnfolded branch') in
              refine_type env t t'

            else
              raise Inconsistent

        | _ ->
            raise Inconsistent

        end

    | TyForall _, _
    | _, TyForall _
    | TyExists _, _
    | _, TyExists _ ->
        Log.error "Don't know how to refine in the presence of quantifiers. We should think\
          about it hard."

    | TyAnchoredPermission _, _
    | _, TyAnchoredPermission _
    | TyEmpty, _
    | _, TyEmpty
    | TyStar _, _
    | _, TyStar _ ->
        Log.error "We can only refine types that have kind TYPE."

    | _ ->
        (* TEMPORARY this seems overly aggressive and expensive *)
        if equal env t1 t2 then
          env, One t1
        else
          (* If there's nothing we can say, keep both. *)
          env, Both

  with Inconsistent ->

    let open TypePrinter in
    Log.debug ~level:4 "Inconsistency detected %a cannot coexist with %a"
      pdoc (ptype, (env, t1)) pdoc (ptype, (env, t2));

    (* We could possibly be smarter here, and mark the entire permission soup as
     * being inconsistent. This would allow us to implement some sort of
     * [absurd] construct that asserts that the program point is not reachable. *)
    env, Both


(* [refine env p t] adds [t] to the list of available permissions for [p],
 * possibly by refining some of these permissions into more precise ones. *)
and refine (env: env) (point: point) (t': typ): env =
  let { permissions } = permissions_for_ident env point in
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
  replace_expr env point (fun _ -> { permissions })


(* [unify env p1 p2] merges two points, and takes care of dealing with how the
 * permissions should be merged. *)
and unify (env: env) (p1: point) (p2: point): env =
  let env =
    List.fold_left (fun env t -> refine env p1 t) env (permissions_for_ident env p2).permissions
  in
  merge_left env p1 p2


(* [add env point t] adds [t] to the list of permissions for [p], performing all
 * the necessary legwork. *)
and add (env: env) (point: point) (t: typ): env =
  let hint = name_for_expr env point in
  let env, t = unfold env ?hint t in
  refine env point t
;;
