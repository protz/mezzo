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

open Kind
open TypeCore
open DeBruijn
open Types
open Derivations

type result = env option * derivation

(* -------------------------------------------------------------------------- *)

(* This should help debugging. *)

let safety_check env =
  (* Be paranoid, perform an expensive safety check. *)
  if Log.debug_level () >= 5 then begin
    fold_terms env (fun () var permissions ->
      (* Each term should have exactly one singleton permission. If we fail here,
       * this is SEVERE: this means one of our internal invariants broken, so
       * someone messed up the code somewhere. *)
      let singletons = List.filter (function
        | TySingleton (TyOpen _) ->
            true
        | _ ->
            false
      ) permissions in
      if List.length singletons <> 1 then
        Log.error
          "%a inconsistency detected: not one singleton type for %a\n%a\n"
          Lexer.p (location env)
          TypePrinter.pnames (env, get_names env var)
          TypePrinter.penv env;

      (* The inconsistencies below are suspicious, but it may just be that we
       * failed to mark the environment as inconsistent. *)

      (* Unless the environment is inconsistent, a given type should have no
       * more than one concrete type. It may happen that we fail to detect this
       * situation and mark the environment as inconsistent, so this check will
       * explode, and remind us that this is one more situation that will mark an
       * environment as inconsistent. *)
      let concrete = List.filter (function
        | TyConcrete _ ->
            true
        | TyTuple _ ->
            true
        | _ ->
            false
      ) permissions in
      (* This part of the safety check is disabled because it is too restrictive,
       * see [twostructural.mz] for an example. *)
      if false && not (is_inconsistent env) && List.length concrete > 1 then
        Log.error
          "%a inconsistency detected: more than one concrete type for %a\n\
            (did you add a function type without calling \
            [simplify_function_type]?)\n%a\n"
          Lexer.p (location env)
          TypePrinter.pnames (env, get_names env var)
          TypePrinter.penv env;

      let exclusive = List.filter (FactInference.is_exclusive env) permissions in
      if not (is_inconsistent env) && List.length exclusive > 1 then
        Log.error
          "%a inconsistency detected: more than one exclusive type for %a\n%a\n"
          Lexer.p (location env)
          TypePrinter.pnames (env, get_names env var)
          TypePrinter.penv env;

      List.iter (internal_checklevel env) permissions;
    ) ();
    List.iter (internal_checklevel env) (get_floating_permissions env);
  end
;;


(* ---------------------------------------------------------------------------- *)

(* When we learn that "a" turns out to be exclusive, new permissions become
 * available. For instance, if we previously had "x @ a", we now have
 * "x @ a ∗ x @ dynamic". *)

let refresh_facts env =
  fold_terms env (fun env var permissions ->
    if List.exists (FactInference.is_exclusive env) permissions &&
       not (List.exists (equal env TyDynamic) permissions) then
      set_permissions env var (TyDynamic :: permissions)
    else
      env
  ) env
;;


(* ---------------------------------------------------------------------------- *)


(** Re-wrap instantiate_flexible so that it fits in our framework. *)

let j_flex_inst (env: env) (v: var) (t: typ): result =
  let judgement = JEqual (TyOpen v, t) in
  match instantiate_flexible env v t with
  | Some sub_env ->
      apply_axiom env judgement "Instantiate" sub_env
  | None ->
      no_proof env judgement
;;

let j_merge_left (env: env) (v1: var) (v2: var): result =
  let judgement = JEqual (TyOpen v1, TyOpen v2) in
  match merge_left env v1 v2 with
  | Some sub_env ->
      apply_axiom env judgement "Merge-Left" sub_env
  | None ->
      no_proof env judgement
;;



(* -------------------------------------------------------------------------- *)

(* Dealing with floating permissions.
 *
 * Floating permissions are permission variables that are available in the
 * environment. They may be abstract or flexible, but in any case, we can't
 * attach them to an identifier, since they're variables. Therefore, they are
 * treated differently. The various [add_perm] and [sub_perm] function will case
 * these two helpers. *)


(* Attention! This function should not be called directly. Even if you know that
 * your permission is a floating one, please call [add_perm] so that the type
 * gets run through [modulo_flex] and [expand_if_one_branch]. *)
let add_floating_perm env t =
  let floating_permissions = get_floating_permissions env in
  set_floating_permissions env (t :: floating_permissions)
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

(* -------------------------------------------------------------------------- *)

let perm_not_flex env t =
  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in
  match t with
  | TyAnchoredPermission (x, _) ->
      not (is_flexible env !!x)
  | TyOpen p ->
      not (is_flexible env p)
  | _ ->
      true
;;

(** Wraps [p] in a bar so that we send this operation into the awesome
 * [add_sub] pipeline. *)
let wrap_bar_perm p =
  TyBar (TyUnknown, p)
;;

(** Wraps "t1" into "∃x.(=x|x@t1)". This is really useful because if this is
 * meant to be added afterwards, then [t1] will be added in expanded form with a
 * free call to [unfold]! *)
let wrap_bar t1 =
  let binding = Auto (Utils.fresh_var "sp"), KTerm, location empty_env in
  TyQ (Exists, binding, AutoIntroduced,
    TyBar (
      TySingleton (TyBound 0),
      TyAnchoredPermission (TyBound 0, t1)
        (* I have removed a call to [lift]. There is no need to lift
           the type [t1], provided it is locally closed! That's the
           point of the locally nameless representation. *)
    )
  )
;;

type side = Left | Right

let is_singleton env t =
  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in
  match t with
  | TySingleton _ -> true
  | TyBar (TySingleton _, _) -> true
  | _ -> false
;;

(** This function opens all rigid quantifications inside a type to make sure we
 * don't open up a binding too late. When [side] is [Left], existential bindings
 * are opened as rigid variables; when [side] is [Right], universal bindings are
 * opened as rigid variables. This operation is useful in [sub_type], before
 * we're about to change levels.
 *
 * This function actually does quite a bit of work, in the sense that it
 * performs unfolding on demand: if there is a missing structure point that
 * could potentially be a rigid variable, it creates it... *)

(* TEMPORARY calling [wrap_bar] causes an existential to appear, so it
   seems interesting only if on the Left side. If on the right side, on
   the contrary, it could prevent us from making progress? *)

class open_all_rigid_in (env : env ref) = object (self)

  (* The type environment [env] has type [env ref], and is threaded
     through the traversal. It is continuously extended. *)

  (* Our environment is a pair of [side], which tells us which kind
     of binders (universal or existential) we are supposed to open,
     and [deconstructed], a Boolean flag that is set to [true] when
     a structural type was just deconstructed and we are expected
     to invoke [wrap_bar]. *)
  inherit [side * bool] map as super

  (* We re-implement the main visitor in order to receive a warning
     when new cases appear and in order to share code. *)
  method visit (side, deconstructed) ty =
    let ty = modulo_flex !env ty in
    let ty = expand_if_one_branch !env ty in
    let ty = if deconstructed && not (is_singleton !env ty) && side = Left then wrap_bar ty else ty in
    match ty, side with

    (* We stop at the following constructors. *)

    | TyUnknown, _
    | TyDynamic, _
    | TyBound _, _
    | TyOpen _, _
    | TyApp _, _
    | TyQ (Forall, _, _, _), Left
    | TyQ (Exists, _, _, _), Right
    | TySingleton _, _
    | TyArrow _, Left
    | TyEmpty, _ ->
        ty

    (* A universal quantifier on the right-hand side gives rise to a rigid
       variable. The type environment is extended. The quantifier disappears.
       The case of an existential on the left-hand side is symmetric. *)

    | TyQ (Forall, binding, _, ty), Right
    | TyQ (Exists, binding, _, ty), Left ->
       let new_env, ty, _ = bind_rigid_in_type !env binding ty in
       env := new_env;
       self#visit (side, false) ty

    (* As a special case, when we find [t -> u] on the right-hand side,
       we go look for existential quantifiers inside [t], and hoist them
       out, where they become universal quantifiers and are opened.
       This amounts to applying the subtyping rule forall a.(t -> u)
       <= (exists a.t) -> u, I believe. Indeed, the original goal was
       to prove that some value has type (exists a.t) -> u, and we are
       replacing it with the goal of proving that this value has type
       t -> u, for a rigid a. *)

    (* Note that we do *not* go down into [u]. That would amount to
       applying the subtyping rule forall a. t -> u <= t -> forall a.u,
       which is incorrect, as it violates the value restriction. *)

    (* This is in fact the only occasion where [side] changes, and it
       changes only from [Right] to [Left]. *)

    | TyArrow (ty1, ty2), Right ->
       let ty1 = self#visit (Left, false) ty1 in
       TyArrow (ty1, ty2)

    (* We descend into the following constructs. *)

    | TyTuple _, _
    | TyConcrete _, _ ->
        super#visit (side, true) ty
        (* Setting [deconstructed] to [true] forces the fields to
          become named with a point, if they weren't already. *)

    | TyBar _, _
        (* I feel like, just like we're descending into the right-hand side of
         * "x @ t", we should descend into "t" inside "(t|P)". What about the
         * rigid variables contained in "(int, int) | P"? However, doing this
         * causes several failures... *)
    | TyStar _, _ ->
        super#visit (side, false) ty

    (* We descend into the right-hand side of [TyAnchoredPermission] and [TyAnd]. *)

    | TyAnchoredPermission (ty1, ty2), _ ->
        TyAnchoredPermission (ty1, self#visit (side, false) ty2)
    | TyAnd (c, ty), _ ->
        TyAnd (c, self#visit (side, false) ty)

  (* At [TyConcrete], we descend into the fields, but not into
     the datacon or into the adopts clause. *)
    method resolved_branch env branch =
    { branch with
      branch_fields = List.map (self#field env) branch.branch_fields;
    }

  (* At physical fields, we set [deconstructed] to [true]. At permission
     fields, we do not; it makes sense only at kind [type]. *)
  method field (side, _) = function
    | FieldValue (field, ty) ->
        FieldValue (field, self#visit (side, true) ty)
        (* Setting [deconstructed] to [true] forces the fields to
          become named with a point, if they weren't already. *)
    | FieldPermission p ->
        FieldPermission (self#visit (side, false) p)

end

let open_all_rigid_in (env : env) (ty : typ) (side : side) : env * typ =
  let env = ref env in
  let ty = (new open_all_rigid_in env) # visit (side, false) ty in
  !env, ty

(** [unify env p1 p2] merges two vars, and takes care of dealing with how the
    permissions should be merged. *)
let rec unify (env: env) (p1: var) (p2: var): env =
  Log.check (is_term env p1 && is_term env p2) "[unify p1 p2] expects [p1] and \
    [p2] to be variables with kind term, not type";

  if same env p1 p2 then
    env
  else
   (* We need to first merge the environment, otherwise this will go into an
     * infinite loop when hitting the TySingletons... *)
    let perms = if is_flexible env p2 then [] else get_permissions env p2 in
    match merge_left env p1 p2 with
    | Some env ->
        List.fold_left (fun env t -> add env p1 t) env perms
    | None ->
        (* So far, only happens when subtracting the context-provided type from
         * the return type of a function. *)
        env

and keep_only_duplicable env =
  let env = fold_terms env (fun env var permissions ->
    let permissions = List.filter (FactInference.is_duplicable env) permissions in
    let env = set_permissions env var permissions in
    env
  ) env in

  (* Don't forget the abstract perm variables. *)
  let floating = get_floating_permissions env in
  let floating = List.filter (FactInference.is_duplicable env) floating in
  let env = set_floating_permissions env floating in

  env


(** [add env var t] adds [t] to the list of permissions for [p], performing all
    the necessary legwork. *)
and add (env: env) (var: var) (t: typ): env =
  Log.check (is_term env var) "You can only add permissions to a var that \
    represents a program identifier.";

  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in

  if is_flexible env var then begin
    Log.debug ~level:1 "Notice: not adding %a to %a because its \
      left-hand side is flexible"
      TypePrinter.ptype (env, TyOpen var)
      TypePrinter.ptype (env, t);
    env

  end else

    (* We first perform unfolding, so that constructors with one branch are
     * simplified. [unfold] calls [add] recursively whenever it adds new vars. *)
    let env, t = open_all_rigid_in env t Left in

    (* Break this up into a type + permissions. *)
    let t, perms = collect t in

    TypePrinter.(Log.debug ~level:4 "%s[%sadding to %a] %a"
      Bash.colors.Bash.red Bash.colors.Bash.default
      pnames (env, get_names env var)
      ptype (env, t));

    (* Add the permissions. *)
    let env = add_perms env perms in

    (* There are several cases that we can optimize for, but here's the default
     * one to start with: *)
    let default env =
      (* Add the "bare" type. Recursive calls took care of calling [add]. *)
      let env = add_type env var t in
      safety_check env;

      env
    in

    begin match t with
    | TySingleton (TyOpen p) when not (same env var p) ->
        Log.debug ~level:4 "%s]%s (singleton)" Bash.colors.Bash.red Bash.colors.Bash.default;
        unify env var p

    | TyQ (Exists, binding, _, t) ->
        Log.debug ~level:4 "%s]%s (exists)" Bash.colors.Bash.red Bash.colors.Bash.default;
        let env, t, _ = bind_rigid_in_type env binding t in
        add env var t

    | TyAnd (c, t) ->
        Log.debug ~level:4 "%s]%s (and-constraints)" Bash.colors.Bash.red Bash.colors.Bash.default;
        let env = FactInference.assume env c in
        let env = refresh_facts env in
        add env var t

    (* This implements the rule "x @ C { f⃗⃗: =y⃗ } * x @ C { f⃗: =y⃗' } implies y⃗ = * y⃗'" *)
    | TyConcrete branch ->
        let original_perms = get_permissions env var in
        begin match MzList.find_opt (function
          | TyConcrete branch' when resolved_datacons_equal env branch.branch_datacon branch'.branch_datacon ->
              Some branch'
          | _ -> None)
          original_perms
        with
        | Some _ when FactInference.is_exclusive env t ->
           Log.debug ~level:4 "%s]%s (two exclusive perms!)" Bash.colors.Bash.red Bash.colors.Bash.default;
           (* We cannot possibly have two exclusive permissions for [x]. *)
            mark_inconsistent env
        | Some branch' ->
           (* If we are still here, then the two permissions at hand are
              not exclusive. This implies, I think, that the two adopts
              clauses must be bottom. So, there is no need to try and
              compute their meet (good). *)
           assert (equal env branch.branch_adopts ty_bottom);
           assert (equal env branch'.branch_adopts ty_bottom);
           List.fold_left2 (fun env f1 f2 ->
             match f1, f2 with
             | FieldValue (f, t), FieldValue (f', t') when Field.equal f f' ->
                  let t = modulo_flex env t in
                  let t = expand_if_one_branch env t in
                begin match t with
                | TySingleton (TyOpen p) ->
                    add env p t'
                | _ ->
                    Log.error "Type not unfolded"
                end
             | _ ->
                Log.error "Datacon order invariant not respected"
           ) env branch.branch_fields branch'.branch_fields
        | None ->
            add_type env var t
        end

    (* This implements the rule "x @ (=y, =z) * x @ (=y', =z') implies y = y' and z * = z'" *)
    | TyTuple ts ->
        let original_perms = get_permissions env var in
        begin match MzList.find_opt (function TyTuple ts' -> Some ts' | _ -> None) original_perms with
        | Some ts' ->
            if List.length ts <> List.length ts' then
              mark_inconsistent env
            else
              List.fold_left2 (fun env t t' ->
                let t = modulo_flex env t in
                let t = expand_if_one_branch env t in
                match t with
                | TySingleton (TyOpen p) ->
                    add env p t'
                | _ ->
                    Log.error "Type not unfolded"
              ) env ts ts'
        | None ->
            add_type env var t
        end

    (* This implements the rule "x @ Cons { head = h; tail = t } ∗ x @ list a" implies "x @ Cons
     * { ... } ∗ x @ Cons { head: a; tail: list a }". After using that rule, the
     * other special rule above will be applied immediately, resulting in extra
     * permissions for [h] and [t]. This is necessary for the [species.mz]
     * example. *)
    | TyApp (t, ts) ->
        let original_perms = get_permissions env var in
        let t = !!t in
        begin match MzList.find_opt (function
          | TyConcrete { branch_datacon = (t', datacon); _ } ->
              if same env t !!t' then
                Some datacon
              else
                None
          | _ ->
              None
        ) original_perms with
        | Some datacon ->
            let branch = find_and_instantiate_branch env t datacon ts in
            let branch = TyConcrete branch in
            add env var branch
        | None ->
            default env
        end

    | _ ->
        default env
    end


(** [add_perm env t] adds a type [t] with kind KPerm to [env], returning the new
    environment. Attention! Because the [add*] function are not designed a
    faillible, you have to make sure, prior to calling [add*], that the
    permission you're about to add is not flexible (use [perm_not_flex]). The
    [sub*] functions, on the other hand, will gracefully fail if something's
    flexible (use [is_good] to check whether their result is okay). *)
and add_perm (env: env) (t: typ): env =
  Log.check (get_kind_for_type env t = KPerm) "This function only works with types of kind perm.";
  if t <> TyEmpty then
    TypePrinter.(Log.debug ~level:4 "[add_perm] %a" ptype (env, t));

  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in

  match t with
  | TyAnchoredPermission (p, t) as perm ->
      if is_flexible env !!p then
        (* We should be able to handle adding [x* = y*] into the environment
         * when both are flexible. However, adding [x* @ τ] into the environment
         * is in general not possible. *)
        if is_singleton env t then
          add env !!p t
        else begin
          Log.debug ~level:1 "Notice: not adding permission %a because its \
            left-hand side is flexible"
            TypePrinter.ptype (env, perm);
          env
        end
      else
        add env !!p t
  | TyStar (p, q) ->
      add_perm (add_perm env p) q
  | TyEmpty ->
      env
  | _ ->
      add_floating_perm env t

and add_perms env perms =
  List.fold_left add_perm env perms

and add_perm_raw env p t =
  let permissions = get_permissions env p in
  set_permissions env p (t :: permissions)

(* [add_type env p t] adds [t], which is assumed to be unfolded and collected,
 * to the list of available permissions for [p] *)
and add_type (env: env) (p: var) (t: typ): env =
  if is_good (Log.silent (fun () -> sub env p t)) then begin
    (* We're not re-binding env because this has bad consequences: in
     * particular, when adding a flexible type variable to a var, it
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
      mark_inconsistent env
    end else if FactInference.is_duplicable env t && in_there_already then
      env
    else
      (* Either the type is not duplicable (so we need to add it!), or it is
       * duplicable, but doesn't exist per se (e.g. α flexible with
       * [duplicable α]) in the permission list. Add it. *)
      add_perm_raw env p t

  end else begin
    Log.debug ~level:4 "→ sub did NOT work%s]%s" Bash.colors.Bash.red Bash.colors.Bash.default;
    let env = add_perm_raw env p t in
    (* If we just added an exclusive type to the var, then it automatically
     * gains the [dynamic] type. *)
    if FactInference.is_exclusive env t then
      add_type env p TyDynamic
    else
      env
  end


(** [sub env var t] tries to extract [t] from the available permissions for
    [var] and returns, if successful, the resulting environment. This is one of
    the two "sub" entry points that this module exports.*)
and sub (env: env) (var: var) ?no_singleton (t: typ): result =
  Log.check (is_term env var) "You can only subtract permissions from a var \
    that represents a program identifier.";

  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in

  let judgement = JSubVar (var, t) in
  let try_proof = try_proof env judgement in

  if is_inconsistent env then
    try_proof "Inconsistent" begin
      qed env
    end

  else if is_singleton env t then
    try_proof "Must-Be-Singleton" begin
      sub_type env (ty_equals var) t >>=
      qed
    end

  else
    let permissions = get_permissions env var in

    (* Priority-order potential merge candidates. *)
    let sort = function
      | _ as t when not (FactInference.is_duplicable env t) -> 0
      (* This basically makes sure we never instantiate a flexible variable with a
       * singleton type. The rationale is that we're too afraid of instantiating
       * with something local to a branch, which will then make the [Merge]
       * operation fail (see [merge18.mz] and [merge19.mz]). *)
      | TyUnknown -> 3
      | TySingleton _ -> 2
      | _ -> 1
    in
    let sort x y = sort x - sort y in
    let permissions = List.sort sort permissions in
    let permissions =
      if Option.unit_bool no_singleton then
        List.filter (function TySingleton _ -> false | _ -> true) permissions
      else
        permissions
    in


    try_several
      env
      judgement
      "Try-Perms"
      permissions
      (fun env remaining t_x ->
        (* [t_x] is the "original" type found in the list of permissions for [x].
         * -- see [tests/fact-inconsistency.mz] as to why I believe it's correct
         * to check [t_x] for duplicity and not just [t]. *)
        let env =
          if FactInference.is_duplicable env t_x then
            env
          else
            set_permissions env var remaining
        in
        sub_type env ~no_singleton:() t_x t
      )


and sub_constraint env c : result =
  let mode, t = c in
  try_proof env (JSubConstraint c) "Constraint" begin
    (* [t] can be any type; for instance, if we have
     *  f @ [a] (duplicable a) ⇒ ...
     * then, when "f" is instantiated, "a" will be replaced by anything...
     *)
    if FactInference.has_mode mode env t then qed env else fail
  end

and sub_constraints env cs : result =
  try_proof env (JSubConstraints cs) "Constraints" (
    premises env (List.map (fun c env ->
      sub_constraint env c
    ) cs)
  )

(** When comparing "list (a, b)" with "list (a*, b* )" you need to compare the
 * parameters, but for that, unfolding first is a good idea. This is one of the
 * two "sub" entry points that this module exports. *)
and sub_type_with_unfolding (env: env) (t1: typ) (t2: typ): result =
  try_proof env (JSubType (t1, t2)) "With-Unfolding" begin
    let _, k = Kind.as_arrow (get_kind_for_type env t1) in
    match k with
    | KPerm ->
        sub_type env (wrap_bar_perm t1) (wrap_bar_perm t2) >>=
        qed
    | KTerm ->
        sub_type env t1 t2 >>=
        qed
    | KType ->
        (* We basically turn both [t1] and [t2] into "∃x.(=x | x @ t1)" which will
         * perform the right dance, including unfolding, thanks to our excellent
         * [add_sub] algorithm (self-pat on the back). *)
        sub_type env (wrap_bar t1) (wrap_bar t2) >>=
        qed
    | _ ->
        assert false
  end


(** [sub_type env t1 t2] examines [t1] and, if [t1] "provides" [t2], returns
    [Some env] where [env] has been modified accordingly (for instance, by
    unifying some flexible variables); it returns [None] otherwise.
    
    BEWARE: this is *not* the function that is exported as "sub_type". We export
    "sub_type_with_unfolding" as "sub_type". *)
and sub_type (env: env) ?no_singleton (t1: typ) (t2: typ): result =
  TypePrinter.(
    Log.debug ~level:4 "[sub_type] %a %s—%s %a"
      ptype (env, t1)
      Bash.colors.Bash.red Bash.colors.Bash.default
      ptype (env, t2));

  let t1 = modulo_flex env t1 and t2 = modulo_flex env t2 in

  let judgement = JSubType (t1, t2) in
  let try_proof_root = try_proof env judgement in
  let no_proof_root = no_proof env judgement in

  let t1 = expand_if_one_branch env t1 in
  let t2 = expand_if_one_branch env t2 in

  match t1, t2 with

  (** Trivial case. *)
  | _, _ when equal env t1 t2 ->
      try_proof_root "Equal" (qed env)
  (* TEMPORARY could we get rid of this fast path? 1- it may be inefficient
     2- it may be the only place in the code where we are comparing two types
     for syntactic equality 3- by removing it, we will be able to discover if
     some structural rules are missing below. *)

  (** Easy cases involving flexible variables *)
  | TyOpen v1, _ when is_flexible env v1 ->
      try_proof_root "Flex-L" begin
        j_flex_inst env v1 t2 >>=
        qed
      end

  | _, TyOpen v2 when is_flexible env v2 ->
      try_proof_root "Flex-R" begin
        j_flex_inst env v2 t1 >>=
        qed
      end

  (** Mode constraints. *)

  | TyAnd (c, t1), t2 ->
      try_proof_root "And-L" begin
        let env = FactInference.assume env c in
        let env = refresh_facts env in
        sub_type env t1 t2 >>=
        (* TEMPORARY this rule may be unsound: assuming [c] while proving
           [t2] is fine, but [c] should not *remain* assumed in the final
          environment that is returned. See tests/tyand05.mz. *)
        qed
      end

  | _, TyAnd (c, t2) ->
      try_proof_root "And-R" begin
        (* First do the subtraction, because the constraint may be "duplicable α"
         * with "α" being flexible. *)
        sub_type env t1 t2 >>= fun env ->
        (* And then, hoping that α has been instantiated, check that it satisfies
         * the constraint. *)
        sub_constraint env c >>=
        qed
      end

  (** Higher priority for binding rigid = universal quantifiers. *)

  | _, TyQ (Forall, binding, _, t2) ->
      try_proof_root "Forall-R" begin
        let env, t2, _ = bind_rigid_in_type env binding t2 in
        sub_type env t1 t2 >>=
        qed
      end

  | TyQ (Exists, binding, _, t1), _ ->
      try_proof_root "Exists-L" begin
        let env, t1, _ = bind_rigid_in_type env binding t1 in
        sub_type env t1 t2 >>=
        qed
      end


  (** Lower priority for binding flexible = existential quantifiers. *)

  | TyQ (Forall, binding, _, t1), _ ->
      try_proof_root "Forall-L" begin
        let env, t2 = open_all_rigid_in env t2 Right in
        let env, t1, _ = bind_flexible_in_type env binding t1 in
        sub_type env t1 t2 >>=
        qed
      end

  | _, TyQ (Exists, binding, _, t2) ->
      try_proof_root "Exists-R" begin
        let env, t1 = open_all_rigid_in env t1 Left in
        let env, t2, _ = bind_flexible_in_type env binding t2 in
        sub_type env t1 t2 >>=
        qed
      end


  (** Structural rules *)

  | TyTuple components1, TyTuple components2
    when List.length components1 = List.length components2 ->
    (* TEMPORARY the above [when] clause is sound, but when the two lengths
       do NOT match, we could issue a good error message; for now, we are
       missing this opportunity. *)
      try_proof_root "Tuple" begin
        premises env (List.map2 (fun t1 t2 -> fun env ->
          match t1, t2 with
          | TySingleton (TyOpen p1), TySingleton (TyOpen p2) when is_flexible env p2 ->
              (* This is a fast-path that creates less debug output and makes
               * things easier to understand when reading traces. *)
              j_merge_left env p1 p2
          | TySingleton (TyOpen p1), _ ->
              (* “=x - τ” can always be rephrased as “take τ from the list of
               * available permissions for x” by replacing “τ” with
               * “∃x'.(=x'|x' @ τ)” and instantiating “x'” with “x”. *)
              sub env p1 t2
          | _ ->
              sub_type_with_unfolding env t1 t2
        ) components1 components2)
      end

  | TyConcrete branch1, TyConcrete branch2 ->
      if resolved_datacons_equal env branch1.branch_datacon branch2.branch_datacon then begin
       assert (branch1.branch_flavor = branch2.branch_flavor);
       assert (List.length branch1.branch_fields = List.length branch2.branch_fields);
        try_proof_root "Concrete" begin
          sub_type env branch1.branch_adopts branch2.branch_adopts >>= fun env ->
          premises env (List.map2 (fun f1 f2 -> fun env ->
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
            | TySingleton (TyOpen p1), TySingleton (TyOpen p2) when is_flexible env p2 ->
                j_merge_left env p1 p2
            | TySingleton (TyOpen p1), _ ->
                sub env p1 t2
            | _ ->
                sub_type_with_unfolding env t1 t2
          ) branch1.branch_fields branch2.branch_fields)
        end
      end
      else
        no_proof_root

  (* This rule compares type applications. This works for all sorts of type
   * applications: abstract types, data types, or type abbreviations. This means
   * that we don't always eagerly expand type abbreviations. *)
  | TyApp (cons1, args1), TyApp (cons2, args2) when same env !!cons1 !!cons2 ->
      try_proof_root "Application" begin
        let cons1 = !!cons1 in
        (* We enter a potentially non-linear context here. Only keep duplicable
         * parts. *)
        let sub_env = keep_only_duplicable env in
        premises sub_env (MzList.map2i (fun i arg1 arg2 -> fun sub_env ->
          (* Variance comes into play here as well. The behavior is fairly
           * intuitive. *)
          match variance sub_env cons1 i with
          | Covariant ->
              try_proof sub_env (JLt (arg1, arg2)) "Covariance" begin
                sub_type_with_unfolding sub_env arg1 arg2 >>=
                qed
              end
          | Contravariant ->
              try_proof sub_env (JGt (arg1, arg2)) "Contravariance" begin
                sub_type_with_unfolding sub_env arg2 arg1 >>=
                qed
              end
          | Bivariant ->
              nothing env "Bivariance"
          | Invariant ->
              try_proof sub_env (JEqual (arg1, arg2)) "Invariance" begin
                sub_type_with_unfolding sub_env arg1 arg2 >>= fun sub_env ->
                sub_type_with_unfolding sub_env arg2 arg1 >>=
                qed
              end
        ) args1 args2) >>~ fun sub_env ->
        import_flex_instanciations env sub_env
      end

  (* Now that we've made sure that the type application is not an abbreviation,
   * we can consider folding back the branch. We could reorder this branch
   * anywhere if we had a guard such has "compatible_branch branch1 cons2". *)
  | TyConcrete branch1, TyApp (cons2, args2) ->
      let (cons1, datacon1) = branch1.branch_datacon in
      let var1 = !!cons1 in
      let cons2 = !!cons2 in

      if same env var1 cons2 then begin
        try_proof_root "Fold-L" begin
          let branch2 = find_and_instantiate_branch env cons2 datacon1 args2 in
          (* There may be permissions attached to this branch. *)
          let t2 = TyConcrete branch2 in
          let t2, p2 = collect t2 in
          sub_type env t1 t2 >>= fun env ->
          sub_perms env p2
        end
      end else begin
        no_proof_root
      end

  | TyConcrete branch1, TyOpen var2 ->
      (* This is basically the same as above, except that type applications
       * without parameters are not [TyApp]s, they are [TyOpen]s. *)
      let (cons1, datacon1) = branch1.branch_datacon in
      let var1 = !!cons1 in

      if same env var1 var2 then begin
        try_proof_root "Fold-L-2" begin
          let branch2 = find_and_instantiate_branch env var2 datacon1 [] in
          (* Same as above. *)
          let t2 = TyConcrete branch2 in
          let t2, p2 = collect t2 in
          sub_type env t1 t2 >>= fun env ->
          sub_perms env p2
        end
      end else begin
        no_proof_root
      end

  | TySingleton t1, TySingleton t2 ->
      try_proof_root "Singleton" begin
        sub_type env t1 t2 >>=
        qed
      end

  | TyArrow (t1, t2), TyArrow (t'1, t'2) ->
      try_proof_root "Arrow" begin
        (* This rule basically amounts to performing an η-expansion on function
         * types. Therefore, we strip the environment of its duplicable parts and
         * keep only the instanciations when returning the final result. *)

        (* 1) Check facts as late as possible (the instantiation of a flexible
         * variables may happen only in "t2 - t'2"). *)
        let constraints, t1 = Hoist.extract_constraints env (Hoist.hoist env t1) in

        (* We perform implicit eta-expansion, so again, non-linear context (we're
         * under an arrow). *)
        let clean_env = keep_only_duplicable env in

        (* 2) Let us compare the domains... any kind of information that we
         * learn at this stage will be made available in the codomain. So it's
         * important that we compare domains THEN codomains, and not the
         * opposite. *)
        Log.debug ~level:4 "%sArrow / Arrow, left%s"
          Bash.colors.Bash.red
          Bash.colors.Bash.default;
        sub_type clean_env t'1 t1 >>= fun domain_env ->

        (* 3) And let us compare the codomains... *)
        Log.debug ~level:4 "%sArrow / Arrow, right%s"
          Bash.colors.Bash.red
          Bash.colors.Bash.default;
        sub_type domain_env t2 t'2 >>= fun codomain_env ->

        (* 3b) And now, check that the facts in the domain are satisfied. We do
         * this just now, because the codomain may have performed flexible
         * variable instantiations. However, the codomain may also have brought
         * us some hypotheses which we are not allowed to use! This is tricky. *)
        Log.debug ~level:4 "%sArrow / Arrow, facts%s"
          Bash.colors.Bash.red
          Bash.colors.Bash.default;
        let fact_env = import_flex_instanciations domain_env codomain_env in
        sub_constraints fact_env constraints >>= fun final_env ->

        Log.debug ~level:4 "%sArrow / End -- adding back permissions%s"
          Bash.colors.Bash.red
          Bash.colors.Bash.default;
        qed (import_flex_instanciations env final_env)
      end

  | TyBar _, TyBar _ ->
      try_proof_root "Bar-Vs-Bar" begin
        (* Unless we do this, we can't handle (t|p) - (t|p|p') properly. *)
        let t1, ps1 = collect t1 in
        let t2, ps2 = collect t2 in

        (* This has the nice guarantee that we don't need to worry about flexible
         * PERM variables anymore (hence the call to List.partition a few lines
         * below). *)
        let ps1 = MzList.flatten_map (flatten_star env) ps1 in
        let ps2 = MzList.flatten_map (flatten_star env) ps2 in

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
        let works_for_sub env p2 =
          is_good (sub_perm env p2)
        in

        (* This is the main function. *)
        let rec add_sub env ps1 ps2 k: state =
          match MzList.take_bool (works_for_add env) ps1 with
          | Some (ps1, p1) ->
              Log.debug "About to add %a"
                TypePrinter.ptype (env, p1);
              let sub_env = add_perm env p1 in
              apply_axiom env (JAdd p1) "Add-Sub-Add" sub_env >>= fun env ->
              add_sub env ps1 ps2 k
          | None ->
              match MzList.take_bool (works_for_sub env) ps2 with
              | Some (ps2, p2) ->
                  sub_perm env p2 >>= fun env ->
                  add_sub env ps1 ps2 k
              | None ->
                  k env ps1 ps2
        in

        (* If the rhs is made up of only a single variable, it's a good idea to
         * instantiate it to [ps1] right now. *)
        begin match ps1, ps2 with
        | ps1, [TyOpen var2] when is_flexible env var2 ->
            j_flex_inst env var2 (fold_star ps1) >>=
            qed
        | _ ->

          (* Our new strategy for inferring PERM variables is as follows. We first
           * put the PERM variables aside, perform the add/sub dance, and see what's
           * left. If either side is made up of just one flexible PERM variable,
           * then bingo, we win.
           *
           * FIXME: this works very well when the flexible variable is in [vars1]; when
           * it is in [vars2], chances are, we've added everything from [ps1] into
           * the environment, so we don't know what's left for us to instanciate
           * [ps2] with... first try a syntactic criterion? Only add permissions in
           * [ps1] if they “unlock” something in [ps2]? I don't know...
           *
           * 20130219: the extra match right above us somehow mitigates this
           * problem, but the paragraph above remains relevant. *)
          let vars1, ps1 = List.partition (function TyOpen _ -> true | _ -> false) ps1 in
          let vars2, ps2 = List.partition (function TyOpen _ -> true | _ -> false) ps2 in

          Log.debug ~level:4 "[add_sub] starting with ps1=%a, ps2=%a, vars1=%a, vars2=%a"
            TypePrinter.ptype (env, fold_star ps1)
            TypePrinter.ptype (env, fold_star ps2)
            TypePrinter.ptype (env, fold_star vars1)
            TypePrinter.ptype (env, fold_star vars2);

          (* Try to eliminate as much as we can... *)
          add_sub env ps1 ps2 begin fun env ps1 ps2 ->

          Log.debug ~level:4 "[add_sub] ended up with ps1=%a, ps2=%a, vars1=%a, vars2=%a"
            TypePrinter.ptype (env, fold_star ps1)
            TypePrinter.ptype (env, fold_star ps2)
            TypePrinter.ptype (env, fold_star vars1)
            TypePrinter.ptype (env, fold_star vars2);

          let strip_syntactically_equal env l1 l2 =
            (* This is only useful if there's a bunch of permission variables
             * (or abstract permissions) on each side: clear these up, and try
             * to do something useful with the rest. *)
            let rec sse env left l1 l2 =
              match l1 with
              | [] ->
                  env, left, l2
              | elt :: l1 ->
                  match MzList.take_bool (equal env elt) l2 with
                  | Some (l2, _elt') ->
                      let env = 
                        if FactInference.is_duplicable env elt then
                          add_perm env elt
                        else
                          env
                      in
                      sse env left l1 l2
                  | None ->
                      sse env (elt :: left) l1 l2
            in
            sse env [] l1 l2
          in

          let ps1 = vars1 @ ps1 and ps2 = vars2 @ ps2 in
          let env, ps1, ps2 = strip_syntactically_equal env ps1 ps2 in

          apply_axiom env (JDebug (fold_star ps1, fold_star ps2)) "Remaining-Add-Sub" env >>= fun env ->

          (* And then try to be smart with whatever remains. *)
          match ps1, ps2 with
          | [TyOpen var1 as t1], [TyOpen var2 as t2] ->
              (* Beware! We're doing our own one-on-one matching of permission
               * variables, but still, we need to keep [var1] if it happens to be a
               * duplicable one! So we add it here, and [sub_floating_perm] will
               * remove it or not, depending on the associated fact. *)
              let env = add_perm env t1 in
              begin match is_flexible env var1, is_flexible env var2 with
              | true, false ->
                  j_merge_left env var2 var1
              | false, true ->
                  j_merge_left env var1 var2
              | true, true ->
                  j_merge_left env var1 var2
              | false, false ->
                  if same env var1 var2 then
                    Log.error "This was meant to be solved by [strip_syntactically_equal]!"
                  else
                    no_proof env (JSubType (t1, t2))
              end >>= fun env ->
              sub_perm env t2 >>=
              qed
          | ps1, [TyOpen var2] when is_flexible env var2 ->
              j_flex_inst env var2 (fold_star ps1) >>=
              qed
          | [TyOpen var1], [TyEmpty] when is_flexible env var1 ->
              (* Any instantiation of [var1] would be fine, actually, so don't
               * commit to [TyEmpty]! *)
              nothing env "keep-flex" >>=
              qed
          | [TyOpen var1], ps2 when is_flexible env var1 ->
              (* We could actually instantiate [var1] to something bigger, e.g. the
               * whole universe + [ps2]. Not sure that's a good idea computationally
               * speaking but that would certainly make some more examples work (I
               * guess?)... *)
              j_flex_inst env var1 (fold_star ps2) >>=
              qed
          | [TyAnchoredPermission (x1, t1)], [TyAnchoredPermission (x2, t2)]
              when is_flexible env !!x2 ->
                (* These two are *really* debatable heuristics. *)
                sub_type_with_unfolding env t1 t2 >>= fun env ->
                j_merge_left env !!x2 !!x1 >>=
                qed
          | [TyAnchoredPermission (x1, t1)], [TyAnchoredPermission (x2, t2)]
              when is_flexible env !!x1 ->
                    sub_type_with_unfolding env t1 t2 >>= fun env ->
                    j_merge_left env !!x1 !!x2 >>=
                    qed
          | ps1, [] ->
              (* We may have a remaining, rigid, floating permission. Good for us! *)
              let sub_env = add_perm env (fold_star ps1) in
              apply_axiom env (JAdd (fold_star ps1)) "Add-Sub-Add" sub_env >>= fun env ->
              nothing env "adding-everything" >>=
              qed
          | [], ps2 ->
              (* This is useful if [ps2] is a rigid floating permission, alone, that
               * also happens to be present in our environment. *)
              sub_perms env ps2
          | ps1, ps2 ->
              let ps1, ps1_flex = List.partition (perm_not_flex env) ps1 in
              let sub_env = add_perms env ps1 in
              apply_axiom env (JAdd (fold_star ps1)) "Add-Sub-Add" sub_env >>= fun env ->
              Log.debug ~level:4 "[add_sub] NOTICE: probable pending failure\n  \
                  coud not add: %a\n  \
                  could not sub: %a"
                TypePrinter.ptype (env, fold_star ps1_flex)
                TypePrinter.ptype (env, fold_star ps2);
              sub_perms env ps2
          end
        end
      end

  | TyBar _, t2 ->
      try_proof_root "Wrap-Bar-R" begin
        sub_type env t1 (TyBar (t2, TyEmpty)) >>=
        qed
      end

  | t1, TyBar _ ->
      try_proof_root "Wrap-Bar-L" begin
        sub_type env (TyBar (t1, TyEmpty)) t2 >>=
        qed
      end

  | TySingleton t1, t2 when not (Option.unit_bool no_singleton) ->
      let var = !!t1 in
      try_proof_root "Singleton-Fold" begin
        sub env var ~no_singleton:() t2 >>=
        qed
      end

  | _ ->
      no_proof_root


(** [sub_perm env t] takes a type [t] with kind KPerm, and tries to return the
    environment without the corresponding permission. *)
and sub_perm (env: env) (t: typ): result =
  Log.check (get_kind_for_type env t = KPerm) "This type does not have kind perm";
  if t <> TyEmpty then
    TypePrinter.(Log.debug ~level:4 "[sub_perm] %a" ptype (env, t));

  let try_proof = try_proof env (JSubPerm t) in
  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in
  match t with
  | TyAnchoredPermission (TyOpen p, t') ->
      if is_flexible env p then
        match t' with
        | TySingleton (TyOpen p') ->
            try_proof "Sub-Anchored-Double-Flex" begin
              j_merge_left env p p' >>=
              qed
            end
        | _ ->
            no_proof env (JSubPerm t')
      else
        try_proof "Sub-Anchored" begin
          sub env p t' >>=
          qed
        end
  | TyStar _ ->
      try_proof "Sub-Star" begin
        sub_perms env (flatten_star env t)
      end
  | TyEmpty ->
      try_proof "Sub-Empty" (qed env)
  | TyOpen p when is_flexible env p ->
      j_flex_inst env p TyEmpty
  | _ ->
      sub_floating_perm env t

(* This function returns a [state] so as to not introduce another judgement when
 * proving a series of permissions. If you need a result so as to chain that
 * with something else, use [sub_perm env (fold_star perms)]. *)
and sub_perms (env: env) (perms: typ list): state =
  (* The order in which we subtract a bunch of permission is important because,
   * again, some of them may have their lhs flexible. Therefore, there is a
   * small search procedure here that picks a suitable permission for
   * subtracting. *)
  if List.length perms = 0 then
    qed env
  else
    match MzList.take_bool (fun p -> (is_good (sub_perm env p))) perms with
    | Some (perms, perm) ->
        sub_perm env perm >>= fun env ->
        sub_perms env perms
    | None ->
        no_proof env (JSubPerm (fold_star perms)) >>= fun _ ->
        fail

(* Attention! This function should not be called directly. Even if you know that
 * your permission is a floating one, please call [sub_perm] so that the type
 * gets run through [modulo_flex] and [expand_if_one_branch]. *)
and sub_floating_perm (env: env) (t0: typ): result =
  match t0 with
  | TyQ (Exists, binding, _, t) ->
      try_proof env (JSubFloating t0) "Exists-R" begin
        let env, t, _ = bind_flexible_in_type env binding t in
        sub_perm env t >>=
        qed
      end
  | _ as t ->
      try_several
        env
        (JSubFloating t)
        "Floating-In-Env"
        (get_floating_permissions env)
        (fun env remaining_perms t' ->
          let sub_env =
            if FactInference.is_duplicable env t' then
              env
            else
              set_floating_permissions env remaining_perms
          in
          sub_type sub_env t' t
        )
;;

(** The version we export is actually the one with unfolding baked in. This is
 * the only one the client should use because it makes sure our invariants are
 * respected. *)
let sub_type = sub_type_with_unfolding;;
let sub env var t = sub env var t;;
