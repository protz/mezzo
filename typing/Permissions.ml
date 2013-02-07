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

(** This is the core of the type-checker, where we handle the set of available
 * permissions, subtracting a permission from the environment, adding
 * permissions to the environment. *)

open Types
open TypeErrors

(* -------------------------------------------------------------------------- *)

(* This should help debuggnig. *)

let safety_check env =
  (* Be paranoid, perform an expensive safety check. *)
  if Log.debug_level () >= 5 then
    fold_terms env (fun () point _ ({ permissions; _ }) ->
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
          "%a inconsistency detected: not one singleton type for %a\n%a\n"
          Lexer.p env.location
          TypePrinter.pnames (env, get_names env point)
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
        | TyTuple _ ->
            true
        | _ ->
            false
      ) permissions in
      (* This part of the safety check is disabled because it is too restrictive,
       * see [twostructural.mz] for an example. *)
      if false && not (env.inconsistent) && List.length concrete > 1 then
        Log.error
          "%a inconsistency detected: more than one concrete type for %a\n\
            (did you add a function type without calling \
            [simplify_function_type]?)\n%a\n"
          Lexer.p env.location
          TypePrinter.pnames (env, get_names env point)
          TypePrinter.penv env;

      let exclusive = List.filter (FactInference.is_exclusive env) permissions in
      if not (env.inconsistent) && List.length exclusive > 1 then
        Log.error
          "%a inconsistency detected: more than one exclusive type for %a\n%a\n"
          Lexer.p env.location
          TypePrinter.pnames (env, get_names env point)
          TypePrinter.penv env;
    ) ()
;;


(* -------------------------------------------------------------------------- *)

(* Dealing with floating permissions.
 *
 * Floating permissions are permission variables that are available in the
 * environment. They may be abstract or flexible, but in any case, we can't
 * attach them to an identifier, since they're variables. Therefore, they are
 * treated differently. The various [add_perm] and [sub_perm] function will case
 * these two helpers. *)


let add_floating_perm env t =
  { env with floating_permissions = t :: env.floating_permissions }
;;


(* -------------------------------------------------------------------------- *)

let add_hint hint str =
  match hint with
  | Some (Auto n)
  | Some (User (_, n)) ->
      Some (Auto (Variable.register (Variable.print n ^ "_" ^ str)))
  | None ->
      None
;;

(** [can_merge env t1 p2] tells whether, assuming that [t2] is a flexible
    variable, it can be safely merged with [t1]. This function checks that the
    facts are compatible. *)
let can_merge (env: env) (t1: typ) (p2: point): bool =
  Log.check (is_flexible env p2) "[can_merge] takes a flexible variable as its second parameter";
  (* The mode of an affine variable is understood to be an upper bound on the
   * various modes it can take. Thus, affine means the flexible variable can
   * instantiate with anything. Exclusive means the flexible variable can
   * instantiate with anything that is exclusive or below exclusive (slim, fat,
   * etc.). *)
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
        Log.error "TODO: type variables with kind KPerm"
  | _ ->
      let f2 = get_fact env p2 in
      let f1 = FactInference.analyze_type env t1 in
      fact_leq f1 f2
;;

(** [collect t] returns all the permissions contained in [t] along with the
 * "cleaned up" version of [t]. *)
let collect = TypeOps.collect;;

(** A type may hold in-depth constraints, such as "duplicable a", for instance. *)
let rec collect_constraints t =
  match t with
  | TyBar (t, p) ->
      let t, ct = collect_constraints t in
      let p, cp = collect_constraints p in
      TyBar (t, p), ct @ cp
  | TyStar (p, q) ->
      let p, cp = collect_constraints p in
      let q, cq = collect_constraints q in
      TyStar (p, q), cp @ cq
  | TyTuple ts ->
      let ts, cs = List.split (List.map collect_constraints ts) in
      TyTuple ts, List.flatten cs
  (* FIXME probably TyConcreteUnfolded as well *)
  | TyAnd (cs, t) ->
      let t, cs' = collect_constraints t in
      t, cs @ cs'
  | _ ->
      t, []
;;


(* -------------------------------------------------------------------------- *)

(* For adding new constraints into the environment. *)
let add_constraints env constraints =
  let env = List.fold_left (fun env (f, t) ->
    let f = fact_of_flag f in
    match t with
    | TyPoint p ->
        let f' = get_fact env p in
        if fact_leq f f' then
        (* [f] tells, for instance, that [p] be exclusive *)
          refresh_fact env p f
        else
          env
    | _ ->
        Log.error "FIXME"
  ) env constraints in
  env
;;


let rec perm_not_flex env t =
  match t with
  | TyPoint p when has_structure env p ->
      perm_not_flex env (Option.extract (structure env p))
  | TyAnchoredPermission (x, _) ->
      not (is_flexible env !!x)
  | TyPoint p ->
      not (is_flexible env p)
  | TyStar _ ->
      true
  | TyEmpty ->
      true
  | TyApp _ ->
      true
  | _ ->
      Log.error "You should not call [perm_not_flex] on %a"
        TypePrinter.ptype (env, t)
;;


(** [unify env p1 p2] merges two points, and takes care of dealing with how the
    permissions should be merged. *)
let rec unify (env: env) (p1: point) (p2: point): env =
  Log.check (is_term env p1 && is_term env p2) "[unify p1 p2] expects [p1] and \
    [p2] to be variables with kind term, not type";

  if same env p1 p2 then
    env
  else
   (* We need to first merge the environment, otherwise this will go into an
     * infinite loop when hitting the TySingletons... *)
    let perms = get_permissions env p2 in
    let env = merge_left env p1 p2 in
    List.fold_left (fun env t -> add env p1 t) env perms


(** [keep_only_duplicable env] strips out from [env] all the non-duplicable
   parts, and returns a function that can undo this operation while still
   retaining all the unifications and instanciations that were performed.
*)
and keep_only_duplicable (env: env): env * (env -> env) =
  (* Let [env] be the environment stripped out of all its non-duplicable
   * permissions, and let [all_perms] be the set of all permissions we
   * stripped. *)
  let env, all_perms = fold_terms env (fun (env, acc) point _ { permissions; _ } ->
    let dup = List.filter (FactInference.is_duplicable env) permissions in
    let env =
      replace_term env point (function binding -> { binding with permissions = dup })
    in
    let permissions =
      List.filter (function TySingleton _ | TyUnknown -> false | _ -> true) permissions
    in
    let permissions = List.map (fun t -> TyAnchoredPermission (TyPoint point, t)) permissions in
    env, permissions @ acc
  ) (env, []) in

  (* Don't forget the abstract perm variables. *)
  let all_floating = env.floating_permissions in
  let dup_floating =
    List.filter (FactInference.is_duplicable env) all_floating
  in
  let env = { env with floating_permissions = dup_floating } in

  (* Micro sanity check. *)
  Log.check (List.length dup_floating = 0)
    "As far as I can tell, there's no point in having an abstract duplicable permission...";

  (* Here's what we need to do to restore the environment to its initial state,
   * while still retaining all the unifications that took place. *)
  let restore env =
    let env = fold_terms env (fun env point _ _ ->
      replace_term env point (function binding -> {
        binding with permissions = initial_permissions_for_point point
    })) env in

    let env = Log.silent (fun () ->
      List.fold_left add_perm env all_perms
    ) in
    let env = { env with floating_permissions = all_floating } in

    env
  in

  env, restore



(** [add env point t] adds [t] to the list of permissions for [p], performing all
    the necessary legwork. *)
and add (env: env) (point: point) (t: typ): env =
  Log.check (is_term env point) "You can only add permissions to a point that \
    represents a program identifier.";

  (* The point is supposed to represent a term, not a type. If it has a
   * structure, this means that it's a type variable with kind term that has
   * been flex'd, then instanciated onto something. We make sure in
   * [Permissions.sub] that we're actually merging, not instanciating, when
   * faced with two [TyPoint]s. *)
  Log.check (not (has_structure env point)) "I don't understand what's happening";

  let hint = get_name env point in

  (* We first perform unfolding, so that constructors with one branch are
   * simplified. [unfold] calls [add] recursively whenever it adds new points. *)
  let env, t = unfold env ~hint t in

  (* Break up this into a type + permissions. *)
  let t, perms = collect t in

  (* Simplify the (potentially) function type. Normally, we already did this
   * everywhere it's needed, but if we learnt new information since (e.g.
   * unified variables), this may still be able to do something useful.
   * 20121206: the entire test suite still works if I remove this line, probably
   * because everything [TypeOps] can figure out, the subtraction can figure out
   * too later on. I'm still leaving it in because 1) someone may forget to call
   * this function in some other context, 2) it will make types smaller, which
   * is better for debugging, and 3) it's not that expensive because I believe
   * types are relatively small. *)
  let t, _ = TypeOps.prepare_function_type env t None in

  TypePrinter.(Log.debug ~level:4 "%s[%sadding to %a] %a"
    Bash.colors.Bash.red Bash.colors.Bash.default
    pnames (env, get_names env point)
    ptype (env, t));

  (* Add the permissions. *)
  let env = List.fold_left add_perm env perms in

  begin match t with
  | TyPoint p when has_structure env p ->
      Log.debug ~level:4 "%s]%s (structure)" Bash.colors.Bash.red Bash.colors.Bash.default;
      add env point (Option.extract (structure env p))

  | TySingleton (TyPoint p) when not (same env point p) ->
      Log.debug ~level:4 "%s]%s (singleton)" Bash.colors.Bash.red Bash.colors.Bash.default;
      unify env point p

  | TyExists (binding, t) ->
      Log.debug ~level:4 "%s]%s (exists)" Bash.colors.Bash.red Bash.colors.Bash.default;
      begin match binding with
      | _, KTerm, _ ->
          let env, t = bind_var_in_type env binding t in
          add env point t
      | _ ->
          Log.error "I don't know how to deal with an existentially-quantified \
            type or permission";
      end

  | TyAnd (constraints, t) ->
      Log.debug ~level:4 "%s]%s (and-constraints)" Bash.colors.Bash.red Bash.colors.Bash.default;
      let env = add_constraints env constraints in
      add env point t

  | _ ->
      (* Add the "bare" type. Recursive calls took care of calling [add]. *)
      let env = add_type env point t in
      safety_check env;

      env
  end


(** [add_perm env t] adds a type [t] with kind KPerm to [env], returning the new
    environment. *)
and add_perm (env: env) (t: typ): env =
  Log.check (get_kind_for_type env t = KPerm) "This function only works with types of kind perm.";
  if t <> TyEmpty then
    TypePrinter.(Log.debug ~level:4 "[add_perm] %a" ptype (env, t));

  match t with
  | TyAnchoredPermission (p, t) ->
      Log.check (not (is_flexible env !!p))
        "Do NOT add a permission whose left-hand-side is flexible.";
      add env !!p t
  | TyStar (p, q) ->
      add_perm (add_perm env p) q
  | TyEmpty ->
      env
  | TyPoint p when has_structure env p ->
      add_perm env (Option.extract (structure env p))
  | _ ->
      add_floating_perm env t


(* [add_type env p t] adds [t], which is assumed to be unfolded and collected,
 * to the list of available permissions for [p] *)
and add_type (env: env) (p: point) (t: typ): env =
  match Log.silent (fun () -> sub env p t) with
  | Some _ ->
      (* We're not re-binding env because this has bad consequences: in
       * particular, when adding a flexible type variable to a point, it
       * instantiates it into, say, [=x], which is usually *not* what we want to
       * do. Happens mostly when doing higher-order, see impredicative.mz or
       * list-map2.mz for examples. *)
      Log.debug ~level:4 "→ sub worked%s]%s" Bash.colors.Bash.red Bash.colors.Bash.default;
      let in_there_already =
        List.exists (fun x -> equal env x t) (get_permissions env p)
      in
      if FactInference.is_exclusive env t then begin
        (* If [t] is exclusive, then this makes the environment inconsistent. *)
        Log.debug ~level:4 "%sInconsistency detected%s, adding %a as an exclusive \
            permission, but it's already available."
          Bash.colors.Bash.red Bash.colors.Bash.default
          TypePrinter.ptype (env, t);
        { env with inconsistent = true }
      end else if FactInference.is_duplicable env t && in_there_already then
        env
      else
        (* Either the type is not duplicable (so we need to add it!), or it is
         * duplicable, but doesn't exist per se (e.g. α flexible with
         * [duplicable α]) in the permission list. Add it. *)
        replace_term env p (fun binding ->
          { binding with permissions = t :: binding.permissions }
        )
  | None ->
      Log.debug ~level:4 "→ sub did NOT work%s]%s" Bash.colors.Bash.red Bash.colors.Bash.default;
      let env =
        replace_term env p (fun binding ->
          { binding with permissions = t :: binding.permissions }
        )
      in
      (* If we just added an exclusive type to the point, then it automatically
       * gains the [dynamic] type. *)
      if FactInference.is_exclusive env t then
        add_type env p TyDynamic
      else
        env


(** [unfold env t] returns [env, t] where [t] has been unfolded, which
    potentially led us into adding new points to [env]. The [hint] serves when
    making up names for intermediary variables. *)
and unfold (env: env) ?(hint: name option) (t: typ): env * typ =
  (* This auxiliary function takes care of inserting an indirection if needed,
   * that is, a [=foo] type with [foo] being a newly-allocated [point]. *)
  let insert_point (env: env) ?(hint: name option) (t: typ): env * typ =
    let hint = Option.map_none (fresh_auto_var "t_") hint in
    match t with
    | TySingleton _ ->
        env, t
    | _ ->
        (* The [expr_binder] also serves as the binder for the corresponding
         * term type variable. *)
        let env, p = bind_term env hint env.location false in
        (* This will take care of unfolding where necessary. *)
        let env = add env p t in
        env, ty_equals p
  in

  let rec unfold (env: env) ?(hint: name option) (t: typ): env * typ =
    match t with
    | TyUnknown
    | TyDynamic
    | TySingleton _
    | TyArrow _
    | TyEmpty ->
        env, t

    | TyPoint _
    | TyApp _ ->
        begin match expand_if_one_branch env t with
        | TyConcreteUnfolded _ as t->
            unfold env t
        | _ ->
            env, t
        end

    | TyVar _ ->
        Log.error "No unbound variables allowed here"

    | TyForall _
    | TyExists _ ->
        env, t

    | TyStar _ ->
        env, t

    | TyBar (t, p) ->
        let env, t = unfold env ?hint t in
        env, TyBar (t, p)

    | TyAnchoredPermission _ ->
        env, t

    (* We're only interested in unfolding structural types. *)
    | TyTuple components ->
        let env, components = Hml_List.fold_lefti (fun i (env, components) component ->
          let hint = add_hint hint (string_of_int i) in
          let env, component = insert_point env ?hint component in
          env, component :: components
        ) (env, []) components in
        env, TyTuple (List.rev components)

    | TyConcreteUnfolded (datacon, fields, clause) ->
        (* If this is a user-provided type (e.g. a function parameter's type) we
         * should not blindly accept this type when adding it into our
         * environment. *)
        let all_fields_there =
          let _, def, _ = def_for_datacon env datacon in
          let _, branch = List.find (fun (datacon', _) -> Datacon.equal (snd datacon) datacon') def in
          let field_name = function
            | FieldValue (name, _) -> Some name
            | FieldPermission _ -> None
          in
          let fields' = Hml_List.map_some field_name branch in
          let fields = Hml_List.map_some field_name fields in
          List.length fields = List.length fields' &&
          List.for_all (fun field' ->
            List.exists (Field.equal field') fields
          ) fields'
        in
        if not (all_fields_there) then
          raise_error env (FieldMismatch (t, (snd datacon)));
        (* It's fine, add it! *)
        let env, fields = List.fold_left (fun (env, fields) -> function
          | FieldPermission _ as field ->
              env, field :: fields
          | FieldValue (name, field) ->
              let hint =
                add_hint hint (Hml_String.bsprintf "%a_%a" Datacon.p (snd datacon) Field.p name)
              in
              let env, field = insert_point env ?hint field in
              env, FieldValue (name, field) :: fields
        ) (env, []) fields
        in
        env, TyConcreteUnfolded (datacon, List.rev fields, clause)

    | TyAnd _
    | TyImply _ ->
        env, t

  in
  unfold env ?hint t


(** [sub env point t] tries to extract [t] from the available permissions for
    [point] and returns, if successful, the resulting environment. *)
and sub (env: env) (point: point) (t: typ): env option =
  Log.check (is_term env point) "You can only subtract permissions from a point \
    that represents a program identifier.";

  (* See the explanation in [add]. *)
  Log.check (not (has_structure env point)) "I don't understand what's happening";

  if env.inconsistent then
    Some env
  else
    (* Get a "clean" type without nested permissions. *)
    let t, perms = collect t in
    let perms = List.flatten (List.map flatten_star perms) in

    (* Start off by subtracting the type without associated permissions. *)
    let env = sub_clean env point t in

    env >>= fun env ->
    sub_perms env perms


(** [sub_clean env point t] takes a "clean" type [t] (without nested permissions)
    and performs the actual work of extracting [t] from the list of permissions
    for [point]. *)
and sub_clean (env: env) (point: point) (t: typ): env option =
  if (not (is_term env point)) then
    Log.error "[KindCheck] should've checked that for us";
  Log.check (not (has_structure env point)) "Strange";

  let permissions = get_permissions env point in

  (* Priority-order potential merge candidates. *)
  let sort = function
    | _ as t when not (FactInference.is_duplicable env t) -> 0
    (* This basically makes sure we never instantiate a flexible variable with a
     * singleton type. The rationale is that we're too afraid of instantiating
     * with something local to a branch, which will then make the [Merge]
     * operation fail (see [merge18.mz] and [merge19.mz]). *)
    | TySingleton _ -> 3
    | TyUnknown -> 2
    | _ -> 1
  in
  let sort x y = sort x - sort y in
  let permissions = List.sort sort permissions in

  let debug env hd t duplicable =
    let open TypePrinter in
    let open Bash in
    let f1 = FactInference.analyze_type env hd in
    let f2 = FactInference.analyze_type env t in
    Log.check
      (fact_leq f1 f2)
      "Fact inconsistency %a is %a <= %a is %a"
      ptype (env, hd)
      pfact f1
      ptype (env, t)
      pfact f2;
    Log.debug ~level:4 "%sTaking%s %a out of the permissions for %a \
      (really? %b)"
      colors.yellow colors.default
      ptype (env, t)
      pvar (env, get_name env point)
      (not duplicable);
  in

  (* [take] proceeds left-to-right *)
  match Hml_List.take (fun x -> sub_type env x t) permissions with
  | Some (remaining, (t_x, env)) ->
      (* [t_x] is the "original" type found in the list of permissions for [x].
       * -- see [tests/fact-inconsistency.mz] as to why I believe it's correct
       * to check [t_x] for duplicity and not just [t]. *)
      let duplicable = FactInference.is_duplicable env t_x in
      debug env t_x t duplicable;
      if duplicable then
        Some env
      else
        Some (replace_term env point (fun binder ->
          { binder with permissions = remaining }))
  | None ->
      None


(** [sub_type env t1 t2] examines [t1] and, if [t1] "provides" [t2], returns
    [Some env] where [env] has been modified accordingly (for instance, by
    unifying some flexible variables); it returns [None] otherwise. *)
and sub_type (env: env) (t1: typ) (t2: typ): env option =
  step_through_flex env sub_type_real t1 t2 ||| sub_type_real env t1 t2

and sub_constraints env constraints =
  List.fold_left (fun env (f, t) ->
    env >>= fun env ->
    let f = fact_of_flag f in
    (* [t] can be any type; for instance, if we have
     *  f @ [a] (duplicable a) ⇒ ...
     * then, when "f" is instantiated, "a" will be replaced by anything...
     *)
    let f' = FactInference.analyze_type env t in
    let is_ok = fact_leq f' f in
    Log.debug "fact [is_ok=%b] for %a: %a"
      is_ok
      TypePrinter.ptype (env, t) TypePrinter.pfact f';
    (* [f] demands, for instance, that [p] be exclusive *)
    if is_ok then
      Some env
    else
      None
  ) (Some env) constraints

and sub_type_real env t1 t2 =
  TypePrinter.(
    Log.debug ~level:4 "[sub_type] %a %s→%s %a"
      ptype (env, t1)
      Bash.colors.Bash.red Bash.colors.Bash.default
      ptype (env, t2));

  if equal env t1 t2 then
    (Log.debug ~level:5 "↳ fast-path"; Some env)

  else match t1, t2 with

  (** Fail early to tame debug output. *)
  | TyUnknown, _
  | _, TyUnknown
  | TyDynamic, _
  | _, TyDynamic ->
      (* If the call to [equal] didn't succeed, we won't succeed either here. *)
      None

  (** Duplicity constraints. *)

  | TyAnd _, _ ->
      Log.error "Constraints should've been processed when this permission was added"

  | TyImply (constraints, t1), t2 ->
      sub_type env t1 (TyAnd (constraints, t2))

  | _, TyAnd (constraints, t2) ->
      (* First do the subtraction, because the constraint may be "duplicable α"
       * with "α" being flexible. *)
      let t2, perms = collect t2 in
      sub_type env t1 t2 >>= fun env ->
      sub_perms env perms >>= fun env ->
      (* And then, hoping that α has been instantiated, check that it satisfies
       * the constraint. *)
      sub_constraints env constraints

  | t1, TyImply (constraints, t2) ->
      let env = add_constraints env constraints in
      sub_type env t1 t2


  (** Higher priority for binding rigid = universal quantifiers. We have to be
   * conservative: we need to show that this subtraction is valid for all
   * possible instantiations of the variable, so we assume Affine. *)

  | _, TyForall ((binding, _), t2) ->
      let env, t2 = bind_var_in_type env ~fact:Affine binding t2 in
      let t2, perms = collect t2 in
      sub_perm env (fold_star perms) >>= fun env ->
      sub_type env t1 t2

  | TyExists (binding, t1), _ ->
      let env, t1 = bind_var_in_type env ~fact:Affine binding t1 in
      let t1, perms = collect t1 in
      let env = add_perm env (fold_star perms) in
      sub_type env t1 t2


  (** Lower priority for binding flexible = existential quantifiers.
   *
   * Since these are existentially quantified, we have to be
   * conservative, and pick the highest element in the fact lattice. It's the
   * default value. *)

  | TyForall ((binding, _), t1), _ ->
      let env, t1 = bind_var_in_type ~flexible:true ~fact:Affine env binding t1 in
      let t1, perms = collect t1 in
      let env = add_perm env (fold_star perms) in
      sub_type env t1 t2

  | _, TyExists (binding, t2) ->
      let env, t2 = bind_var_in_type ~flexible:true ~fact:Affine env binding t2 in
      let t2, perms = collect t2 in
      sub_type env t1 t2 >>= fun env ->
      sub_perm env (fold_star perms)


  (** Structural rules *)

  | TyTuple components1, TyTuple components2
    when List.length components1 = List.length components2 ->
      List.fold_left2 (fun env t1 t2 ->
        env >>= fun env ->
        match t1, t2 with
        | _ when equal env t1 t2 ->
            (* XXX this should be removed; the reason we have this is we're not
             * always performing proper unfolding on the left-hand-side, and
             * sometimes we're running “(int, int) - (int, int)” -- this is what
             * makes it work *)
            Some env

        | TySingleton (TyPoint p1), _ when is_flexible env p1 ->
            (* The unfolding never, ever introduces flexible variables. *)
            assert false
        | TySingleton (TyPoint p1), TySingleton (TyPoint p2) when is_flexible env p2 ->
            (* This is a fast-path that creates less debug output and makes
             * things easier to understand when reading traces. *)
            Some (merge_left env p1 p2)
        | TySingleton (TyPoint p1), _ ->
            (* “=x - τ” can always be rephrased as “take τ from the list of
             * available permissions for x” by replacing “τ” with
             * “∃x'.(=x'|x' @ τ)” and instantiating “x'” with “x”. *)
            sub_clean env p1 t2

        | TyPoint p1, _ when is_flexible env p1 ->
            (* XXX this should be removed too, the reason we have this is to
             * make “(α, int) - (int, int)” work with “α” flexible. *)
            try_merge_flex env p1 t1
        | _, TyPoint p2 when is_flexible env p2 ->
            (* XXX should be removed too. The reason these two rules come last
             * is that the present match case is good when we know [t1] is not
             * [TySingleton]. *)
            try_merge_flex env p2 t1

        | _ ->
            None
      ) (Some env) components1 components2

  | TyConcreteUnfolded (datacon1, fields1, clause1), TyConcreteUnfolded (datacon2, fields2, clause2)
    when List.length fields1 = List.length fields2 ->
      if resolved_datacons_equal env datacon1 datacon2 then
        sub_type env clause1 clause2 >>= fun env ->
        List.fold_left2 (fun env f1 f2 ->
          env >>= fun env ->
          let t1, t2 =
            match f1, f2 with
            | FieldValue (name1, t1), FieldValue (name2, t2) ->
                Log.check (Field.equal name1 name2) "Not in order?";
                t1, t2
            | _ ->
                Log.error "The type we're trying to extract should've been \
                  cleaned first."
          in
          (* This is the same logic as the [TyTuple] case above, scroll up for
           * comments and detailed explanations as to why these rules are
           * correct. *)
          match t1, t2 with
          | _ when equal env t1 t2 ->
              Some env

          | TySingleton (TyPoint p1), _ when is_flexible env p1 ->
              assert false
          | TySingleton (TyPoint p1), TySingleton (TyPoint p2) when is_flexible env p2 ->
              Some (merge_left env p1 p2)
          | TySingleton (TyPoint p1), _ ->
              sub_clean env p1 t2

          | TyPoint p1, _ when is_flexible env p1 ->
              try_merge_flex env p1 t1
          | _, TyPoint p2 when is_flexible env p2 ->
              try_merge_flex env p2 t1

          | _ ->
              None
        ) (Some env) fields1 fields2

      else
        None

  | TyConcreteUnfolded ((cons1, datacon1), _, _), TyApp (cons2, args2) ->
      let point1 = !!cons1 in
      let cons2 = !!cons2 in

      if same env point1 cons2 then begin
        let datacon2, fields2, clause2 = find_and_instantiate_branch env cons2 datacon1 args2 in
        (* There may be permissions attached to this branch. *)
        let t2 = TyConcreteUnfolded (datacon2, fields2, clause2) in
        let t2, p2 = collect t2 in
        sub_type env t1 t2 >>= fun env ->
        sub_perms env p2
      end else begin
        None
      end

  | TyConcreteUnfolded ((cons1, datacon1), _, _), TyPoint point2 ->
      (* This is basically the same as above, except that type applications
       * without parameters are not [TyApp]s, they are [TyPoint]s. *)
      let point1 = !!cons1 in

      if same env point1 point2 then begin
        (* XXX why are we not collecting permissions here? *)
        let datacon2, fields2, clause2 = find_and_instantiate_branch env point2 datacon1 [] in
        sub_type env t1 (TyConcreteUnfolded (datacon2, fields2, clause2))
      end else begin
        None
      end

  | TyApp (cons1, args1), TyApp (cons2, args2) ->
      let cons1 = !!cons1 in
      let cons2 = !!cons2 in

      if same env cons1 cons2 then
        let env, restore = keep_only_duplicable env in
        Hml_List.fold_left2i (fun i env arg1 arg2 ->
          env >>= fun env ->
          (* Variance comes into play here as well. The behavior is fairly
           * intuitive. *)
          match variance env cons1 i with
          | Covariant ->
              sub_type env arg1 arg2
          | Contravariant ->
              sub_type env arg2 arg1
          | Bivariant ->
              Some env
          | Invariant ->
              sub_type env arg1 arg2 >>= fun env ->
              sub_type env arg2 arg1
        ) (Some env) args1 args2 >>= fun env ->
        Some (restore env)
      else
        None

  | TySingleton t1, TySingleton t2 ->
      sub_type env t1 t2

  | TyArrow (t1, t2), TyArrow (t'1, t'2) ->
      (* This rule basically amounts to performing an η-expansion on function
       * types. Therefore, we strip the environment of its duplicable parts and
       * keep only the instanciations when returning the final result. *)

      (* 1) Get an environment stripped out of all its non-duplicable
       * permissions. *)
      let env, restore = keep_only_duplicable env in

      (* 1b) Check facts as late as possible (the instantiation of a flexible
       * variables may happen only in "t2 - t'2"). *)
      let env, t1, constraints = match t1 with
        | TyAnd (constraints, t1) ->
            env, t1, constraints
        | _ ->
            env, t1, []
      in

      (* 2) Let us compare the domains... *)
      Log.debug ~level:4 "%sArrow / Arrow, left%s"
        Bash.colors.Bash.red
        Bash.colors.Bash.default;
      sub_type env t'1 t1 >>= fun env ->

      (* 3) And let us compare the codomains... *)
      Log.debug ~level:4 "%sArrow / Arrow, right%s"
        Bash.colors.Bash.red
        Bash.colors.Bash.default;
      sub_type env t2 t'2 >>= fun env ->

      (* 3b) Now check facts! *)
      Log.debug ~level:4 "%sArrow / Arrow, facts%s"
        Bash.colors.Bash.red
        Bash.colors.Bash.default;
      sub_constraints env constraints >>= fun env ->

      (* 4) We have successfully compared these function types. Just return the
       * "restored" environment, that is, the environment with the exact same
       * set of original permissions, except that the unifications that took
       * place are now retained. *)
      Log.debug ~level:4 "%sArrow / End -- adding back permissions%s"
        Bash.colors.Bash.red
        Bash.colors.Bash.default;

      Some (restore env)

  | TyBar (t1, p1), TyBar (t2, p2) ->
      (* Unless we do this, we can't handle (t|p) - (t|p|p') properly. *)
      let t1, p'1 = collect t1 in
      let p1 = fold_star (p1 :: p'1) in
      let t2, p'2 = collect t2 in
      let p2 = fold_star (p2 :: p'2) in

      (* "(t1 | p1) - (t2 | p2)" means doing "t1 - t2", adding all of [p1],
       * removing all of [p2]. However, the order in which we perform these
       * operations matters, unfortunately. *)
      Log.debug ~level:4 "[add_sub] entering...";

      (*  All these manipulations are required when doing higher-order, because
       * we need to compare function types, and function types have complicated
       * [TyBar]s for their arguments and return values.
       *  [p1] and [p2] contain permissions such as “x @ τ” where “x” is
       * flexible. Therefore, we need to pick permissions that we know how to
       * add or subtract, that is, permissions for which “x” is rigid.
       *  The algorithm below becomes even more complicated because we need to
       * be smart when [p1] or [p2] contain flexible permission variables: we
       * need to instantiate these in a smart way.
       *  The first step consists in subtracting [t2] from [t1], as most of the
       * time, we're dealing with “(=x|...) - (=x'|...)”. *)
      sub_type env t1 t2 >>= fun env ->

      (* Another subtlety: there may be flexible variables instantiated with
       * something lying around in [p1] or [p2]: we need to get rid of these. *)
      let rec strip_flatten env t =
        match t with
        | TyPoint p ->
            begin match structure env p with
            | Some t ->
                let t = flatten_star t in
                Hml_List.map_flatten (strip_flatten env) t
            | None ->
                [t]
            end
        | TyStar _ ->
            Hml_List.map_flatten (strip_flatten env) (flatten_star t)
        | TyAnchoredPermission (x, t) ->
            let t, ps = collect t in
            if List.length ps > 0 then
              let ps = Hml_List.map_flatten (strip_flatten env) ps in
              TyAnchoredPermission (x, t) :: ps
            else
              [TyAnchoredPermission (x, t)]
        | TyEmpty ->
            []
        | _ ->
            [t]
      in
      let ps1 = strip_flatten env p1 in
      let ps2 = strip_flatten env p2 in

      (*   [add_perm] will fail if we add "x @ t" when "x" is flexible. So we
       * search among the permissions in [ps1] one that is suitable for adding,
       * i.e. a permission whose left-hand-side is not flexible.
       *   But we may be stuck because all permissions in [ps1] have their lhs
       * flexible! However, maybe there's an element in [ps2] that, when
       * subtracted, "unlocks" the situation by instantiating the lhs of one
       * permission in [ps1]. So we alternate adding from [ps1] and subtracting
       * from [ps2] until there's nothing left we can do, either because
       * something's flexible, or because the permissions can't be subtracted. *)
      let works_for_add = perm_not_flex in
      let works_for_sub env p2 = perm_not_flex env p2 && Option.is_some (sub_perm env p2) in

      (* This is the main function. *)
      let rec add_sub env ps1 ps2: env * typ list * typ list =
        match Hml_List.take_bool (works_for_add env) ps1 with
        | Some (ps1, p1) ->
            let env = add_perm env p1 in
            add_sub env ps1 ps2
        | None ->
            match Hml_List.take_bool (works_for_sub env) ps2 with
            | Some (ps2, p2) ->
                let env = Option.extract (sub_perm env p2) in
                add_sub env ps1 ps2
            | None ->
                env, ps1, ps2
      in

      (* Our new strategy for inferring PERM variables is as follows. We first
       * put the PERM variables aside, perform the add/sub dance, and see what's
       * left. If either side is made up of just one flexible PERM variable,
       * then bingo, we win.
       *
       * FIXME: this works very well when the flexible variable is in [vars1]; when
       * it is in [vars2], chances are, we've added everything from [ps1] into
       * the environment, so we don't know what's left for us to instanciate
       * [ps2] with... first try a syntactic criterion? Only add permissions in
       * [ps1] if they “unlock” something in [ps2]? I don't know... *)
      let vars1, ps1 = List.partition (function TyPoint _ -> true | _ -> false) ps1 in
      let vars2, ps2 = List.partition (function TyPoint _ -> true | _ -> false) ps2 in

      Log.debug ~level:4 "[add_sub] starting with ps1=%a, ps2=%a, vars1=%a, vars2=%a"
        TypePrinter.ptype (env, fold_star ps1)
        TypePrinter.ptype (env, fold_star ps2)
        TypePrinter.ptype (env, fold_star vars1)
        TypePrinter.ptype (env, fold_star vars2);

      (* Try to eliminate as much as we can... *)
      let env, ps1, ps2 = add_sub env ps1 ps2 in

      Log.debug ~level:4 "[add_sub] ended up with ps1=%a, ps2=%a, vars1=%a, vars2=%a"
        TypePrinter.ptype (env, fold_star ps1)
        TypePrinter.ptype (env, fold_star ps2)
        TypePrinter.ptype (env, fold_star vars1)
        TypePrinter.ptype (env, fold_star vars2);

      (* And then try to be smart with whatever remains. *)
      begin match vars1 @ ps1, vars2 @ ps2 with
      | [TyPoint var1 as t1], [TyPoint var2 as t2] ->
          (* Beware! We're doing our own one-on-one matching of permission
           * variables, but still, we need to keep [var1] if it happens to be a
           * duplicable one! So we add it here, and [sub_floating_perm] will
           * remove it or not, depending on the associated fact. *)
          let env = add_floating_perm env t1 in
          begin match is_flexible env var1, is_flexible env var2 with
          | true, false ->
              Some (merge_left env var2 var1)
          | false, true ->
              Some (merge_left env var1 var2)
          | true, true ->
              Some (merge_left env var1 var2)
          | false, false ->
              if same env var1 var2 then
                Some env
              else
                None
          end >>= fun env ->
          sub_floating_perm env t2
      | ps1, [TyPoint var2] when is_flexible env var2 ->
          Some (instantiate_flexible env var2 (fold_star ps1))
      | [TyPoint var1], ps2 when is_flexible env var1 ->
          Some (instantiate_flexible env var1 (fold_star ps2))
      | ps1, [] ->
          (* We may have a remaining, rigid, floating permission. Good for us! *)
          Some (add_perm env (fold_star ps1))
      | [], ps2 ->
          (* This is useful if [ps2] is a rigid floating permission, alone, that
           * also happens to be present in our environment. *)
          sub_perms env ps2
      | _, _ ->
          Log.debug ~level:4 "[add_sub] FAILED";
          None
      end

  | TyBar _, t2 ->
      sub_type env t1 (TyBar (t2, TyEmpty))

  | t1, TyBar _ ->
      sub_type env (TyBar (t1, TyEmpty)) t2

  | _ ->
      None


and try_merge_flex env p t =
  if is_flexible env p && can_merge env t p then
    Some (instantiate_flexible env p t)
  else
    None


and try_merge_point_to_point env p1 p2 =
  if is_flexible env p2 then
    Some (merge_left env p1 p2)
  else
    None



(* This function allows you to step-through flexible variables, if there are
 * some. If we did step through something, we recurse through [k]. Otherwise, we
 * fail. *)
and step_through_flex ?(stepped=false) env k t1 t2 =
  let c = step_through_flex ~stepped:true in
  match t1, t2 with
  | TyPoint p1, TyPoint p2 ->
      if same env p1 p2 then
        Some env
      else
        try_merge_point_to_point env p1 p2 |||
        try_merge_point_to_point env p2 p1 |||
        (structure env p1 >>= fun t1 -> c env k t1 t2) |||
        (structure env p2 >>= fun t2 -> c env k t1 t2)

  | TyPoint p1, _ ->
      try_merge_flex env p1 t2 |||
      (structure env p1 >>= fun t1 -> c env k t1 t2)

  | _, TyPoint p2 ->
      try_merge_flex env p2 t1 |||
      (structure env p2 >>= fun t2 -> c env k t1 t2)

  | _ ->
      if stepped then
        k env t1 t2
      else
        None


(** [sub_perm env t] takes a type [t] with kind KPerm, and tries to return the
    environment without the corresponding permission. *)
and sub_perm (env: env) (t: typ): env option =
  Log.check (get_kind_for_type env t = KPerm) "This type does not have kind perm";
  if t <> TyEmpty then
    TypePrinter.(Log.debug ~level:4 "[sub_perm] %a" ptype (env, t));

  match t with
  | TyAnchoredPermission (TyPoint p, t) ->
      sub env p t
  | TyStar _ ->
      sub_perms env (flatten_star t)
  | TyEmpty ->
      Some env
  | TyPoint p when has_structure env p ->
      sub_perm env (Option.extract (structure env p))
  | _ ->
      sub_floating_perm env t

and sub_perms env perms =
  (* The order in which we subtract a bunch of permission is important because,
   * again, some of them may have their lhs flexible. Therefore, there is a
   * small search procedure here that picks a suitable permission for
   * subtracting. *)
  if List.length perms = 0 then
    Some env
  else
    match Hml_List.take_bool (perm_not_flex env) perms with
    | Some (perms, perm) ->
        sub_perm env perm >>= fun env ->
        sub_perms env perms
    | None ->
        Log.debug ~level:4 "[sub_perms] failed, remaining: %a"
          TypePrinter.ptype (env, fold_star perms);
        None

and sub_floating_perm env t =
  match Hml_List.take (sub_type env t) env.floating_permissions with
  | Some (remaining_perms, (t', env)) ->
      if FactInference.is_duplicable env t' then
        Some env
      else
        Some { env with floating_permissions = remaining_perms }
  | None ->
      None
;;

