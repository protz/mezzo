open Kind
open TypeCore
open DeBruijn
module S = SurfaceSyntax

let surface_print_var env = function
  | User (m, x) when Module.equal (module_name env) m ->
      S.Unqualified x
  | User (m, x) ->
      S.Qualified (m, x)
  | Auto x ->
      S.Unqualified x

let surface_print_point env point =
  try
    match surface_print_var env (get_name env point), is_flexible env point with
    | S.Unqualified x, true ->
       S.Unqualified (Variable.register (Variable.print x ^ "*"))
    | _, true ->
       assert false
    | x, false ->
       x
  with UnboundPoint ->
    S.Unqualified (Variable.register "!! ☠ !!")

let resugar_binding env (x, kind, loc) =
  S.destruct_unqualified (surface_print_var env x), kind, loc

(* TEMPORARY
   - is our choice of names hygienic?
   - understand better whether the structure of types is preserved
     throughout the type-checking process
*)

let rec resugar env (points : unit VarMap.t ref) (soup : typ VarMap.t ref) ty =
  match modulo_flex env ty with
  | TyUnknown ->
      S.TyUnknown
  | TyDynamic ->
      S.TyDynamic
  | TyBound _ ->
      assert false
  | TyOpen x ->
      S.TyVar (surface_print_point env x)
  | TyQ (Forall, binding, UserIntroduced, ty) ->
      (* This universal quantifier was introduced by the user. We
         do not attempt it to make it implicit. Furthermore, we
         must not propagate [points] under it, as the scope of
        name introduction forms does not enter quantifiers. *)
      let env, ty, _ = bind_rigid_in_type env binding ty in
      S.TyForall (resugar_binding env binding, reset env ty)
  | TyQ (Forall, _, AutoIntroduced, _)
      (* This universal quantifier was introduced as part of the
        desugaring process, and signals the presence of a desugared
        arrow. *)
  | TyArrow _ ->
      resugar_arrow env VarMap.empty ty
  | TyQ (Exists, binding, _flavor, ty) ->
      (* TEMPORARY use flavor; treated as explicit for now *)
      let env, ty, _ = bind_rigid_in_type env binding ty in
      S.TyExists (resugar_binding env binding, reset env ty)
  | TyApp (head, args) ->
      (* No name introduction is possible inside a type application. *)
      S.TyApp (reset env head, List.map (reset env) args)
  | TyTuple tys ->
      S.TyTuple (List.map (resugar env points soup) tys)
  | TyConcrete branch ->
      resugar_resolved_branch env points soup branch
  | TySingleton (TyOpen x) ->
      (* Construct a name for this variable. *)
      let name = surface_print_point env x in
      (* If this is one the points for which we would like to create
        a [TyNameIntro] introduction form, then create such a form,
        and update [points] by removing [x] from it: this indicates
        success. *)
      if not (is_flexible env x) && VarMap.mem x !points then begin
        points := VarMap.remove x !points;
       (* Try finding a type for this point in the soup. If there
          is one, translate it recursively. This is important, as
          we may be able to create further name introduction forms
          inside it. *)
       let ty =
         try
           let ty = VarMap.find x !soup in
           soup := VarMap.remove x !soup;
           ty
         with Not_found ->
           TyUnknown
       in
       S.TyNameIntro (S.destruct_unqualified name, resugar env points soup ty)
      end
      (* Otherwise, just create a normal singleton type node. *)
      else
       S.TySingleton (S.TyVar name)
  | TySingleton _ ->
      (* Only type variables have kind [KTerm]. *)
      assert false
  | TyBar (ty, TyEmpty) ->
      resugar env points soup ty
  | TyBar (ty, TyStar (p, q)) ->
      resugar env points soup (TyBar (TyBar (ty, p), q))
  | TyBar (ty, TyAnchoredPermission (TyOpen x, t)) ->
      (* Add [x @ t] to the soup, and use it when translating [ty]. *)
      soup := VarMap.add x t !soup;
      resugar env points soup ty
  | TyBar (ty, p) ->
      S.TyBar (resugar env points soup ty, reset env p)
  | TyAnchoredPermission (ty1, ty2) ->
      assert (VarMap.is_empty !points);
      S.TyAnchoredPermission (reset env ty1, reset env ty2)
  | TyEmpty ->
      assert (VarMap.is_empty !points);
      S.TyEmpty
  | TyStar (p1, p2) ->
      assert (VarMap.is_empty !points);
      S.TyStar (reset env p1, reset env p2)
  | TyAnd (c, ty) ->
      S.TyAnd (reset_mode_constraint env c, resugar env points soup ty)

and resugar_arrow env points ty =
  match modulo_flex env ty with
  | TyQ (Forall, ((_, kind, _) as binding), AutoIntroduced, ty) ->
      assert (kind = KTerm);
      (* This universal quantifier was introduced as part of the
        desugaring process. Let's try and make it implicit. We
        expect to find an arrow under it. For the moment, just
        collect this binding and go down. *)
      let env, ty, x = bind_rigid_in_type env binding ty in
      let points = VarMap.add x () points in
      resugar_arrow env points ty
  | TyArrow (ty1, ty2) ->
      (* Here is the arrow that we were expecting to find.
        Translate the domain, expecting that each of the
        points that we have collected will receive a name
        introduction form. *)
      let points = ref points in
      let soup = ref VarMap.empty in
      let ty1 = resugar env points soup ty1 in
      (* This may be too naive. *)
      assert (VarMap.is_empty !points);
      (* TEMPORARY construct TyBar for the remaining soup elements *)
      assert (VarMap.is_empty !soup);
      (* Since every point has been named via a name introduction
        form, there is no need to create explicit universal
        quantifiers. Translate the codomain and build an arrow. *)
      let ty2 = reset env ty2 in
      S.TyArrow (S.TyConsumes ty1, ty2)
  | _ ->
      (* This may be too naive. *)
      assert false

and resugar_resolved_branch env points soup branch =
  (* Recreate a [datacon_reference] for this data constructor. *)
  (* TEMPORARY something is wrong:
     1. it is clumsy to recreate this info; (why did we forget it?)
     2. there seems to be no way of reconstructing a qualified name! *)
  let _, dc = branch.branch_datacon in
  let dref : S.datacon_reference = {
    S.datacon_unresolved = S.Unqualified dc;
    S.datacon_info = None
  } in
  (* Resugar the fields. *)
  let fields = List.map (resugar_field env points soup) branch.branch_fields in
  (* Resugar the adopts clause. If it is [bottom], it becomes [None]. *)
  let clause = Option.map (reset env) (is_non_bottom branch.branch_adopts) in
  (* Done. *)
  S.TyConcrete ((dref, fields), clause)

and resugar_field env points soup = function
  | FieldValue (f, ty) ->
      S.FieldValue (f, resugar env points soup ty)
  | FieldPermission p ->
      S.FieldPermission (reset env p)

and reset_mode_constraint env (mode, ty) =
  mode, reset env ty

and reset env ty =
  let points = ref VarMap.empty in
  let soup = ref VarMap.empty in
  let ty = resugar env points soup ty in
  assert (VarMap.is_empty !points);
  spill_soup env !soup ty

and spill_soup env soup ty =
  VarMap.fold (fun x t ty ->
    S.TyBar (ty, reset env (TyAnchoredPermission (TyOpen x, t)))
  ) soup ty

(* ---------------------------------------------------------------------------- *)

(* The main entry point. *)

let resugar =
  reset

