(* This module translates the surface syntax down to our internal
   representation.

   - All implicit name bindings made through [TyNameIntro] are turned into
     explicit quantifiers, either [TyForall] or [TyExists].
   - Function parameters that are not consumed, when desugared, generate a
     permission in the returned type. [TyConsumes] annotations are removed.
   - Type annotations in patterns are removed, and are attached to let or val
     bindings instead.
   - Location information inside types and patterns is dropped.
*)

open SurfaceSyntax
open KindCheck
open Utils

module T = Types
module E = Expressions

(* let translate_pattern (env: env) (pattern: pattern): pattern =

  let rec extract_constraint (env: env) (pattern: pattern): pattern * typ =
    match pattern with
    | PConstraint (pattern, typ) ->
        let pattern, sub_typ = extract_constraint env pattern in
        begin match sub_typ with
        | TyUnknown ->
            pattern, typ
        | _ ->
            raise_error env (SubPattern pattern)
        end

    | PVar name ->
        PVar name, TyUnknown

    | PPoint point ->
        PPoint point, TyUnknown

    | PTuple pats ->
        let pats, ts = List.split (List.map (extract_constraint env) pats) in
        PTuple pats, TyTuple (List.map (fun x -> TyTupleComponentValue x) ts)

    | PConstruct (name, fieldpats) ->
        let fieldpats, fieldtypes = List.fold_left
          (fun (fieldpats, fieldtypes) (field, pat) ->
            let pat, t = extract_constraint env pat in
            (field, pat) :: fieldpats, (field, t) :: fieldtypes)
          ([], []) fieldpats
        in
        let fieldtypes = List.map (fun x -> FieldValue x) fieldtypes in
        PConstruct (name, fieldpats), TyConcreteUnfolded (name, fieldtypes)


    | PLocated (pattern, p1, p2) ->
        let pattern, typ = extract_constraint (locate env (p1, p2)) pattern in
        PLocated (pattern, p1, p2), typ
  in
  
  let pattern, t = extract_constraint env pattern in
  PConstraint (pattern, t)
;; *)

let fold_forall bindings t =
  List.fold_right (fun binding t ->
    T.TyForall (binding, t)
  ) bindings t
;;

let fold_exists bindings t =
  List.fold_right (fun binding t ->
    T.TyExists (binding, t)
  ) bindings t
;;



let strip_consumes (env: env) (t: typ): typ * type_binding list * typ list =
  (* I don't think it's worth having a tail-rec function here... *)
  let rec strip_consumes env t =
    match t with
    | TyLocated (t, p1, p2) ->
        (* Keep the location information, may be useful later on. *)
        let env = locate env p1 p2 in
        let t, acc = strip_consumes env t in
        TyLocated (t, p1, p2), acc

    | TyTuple ts ->
        let ts, accs = List.split (List.map (strip_consumes env) ts) in
        TyTuple ts, List.flatten accs

    | TyConcreteUnfolded (datacon, fields) ->
        let accs, fields = List.fold_left (fun (accs, fields) field ->
          match field with
          | FieldPermission _ ->
              (accs, field :: fields)
          | FieldValue (name, t) ->
              let t, acc = strip_consumes env t in
              (acc :: accs, FieldValue (name, t) :: fields)
        ) ([], []) fields in
        let fields = List.rev fields in
        let acc = List.flatten accs in
        TyConcreteUnfolded (datacon, fields), acc

    | TyNameIntro (x, t) ->
        let t, acc = strip_consumes env t in
        TyNameIntro (x, t), acc

    | TyBar (t, p) ->
        (* Strip all consumes annotations from [t]. *)
        let t, acc = strip_consumes env t in
        (* Get the permissions contained in [p] as a list. *)
        let perms = flatten_star p in
        (* Some of them are consumed, and should be returned in the accumulator
         * of consumed permissions. Others are kept. *)
        let consumed, kept =
          List.partition (function TyConsumes _ -> true | _ -> false) perms
        in
        let consumed =
          List.map (function TyConsumes p -> None, p | _ -> assert false) consumed
        in
        let p = fold_star kept in
        (* Minimal cleanup. *)
        (if List.length kept > 0 then TyBar (t, p) else t),
        acc @ consumed

    | TyConsumes t ->
        let name = Variable.register (fresh_name "/c") in
        let perm = TyAnchoredPermission (TyVar name, t) in
        ty_equals name, [Some name, perm]

    | TyUnknown
    | TyDynamic
    | TyVar _
    | TySingleton _
    (* These are opaque, no consumes annotations inside of these. *)
    | TyForall _
    | TyApp _
    | TyArrow _ ->
        t, []

    (* Permissions *)
    | TyAnchoredPermission _
    | TyEmpty
    | TyStar _ ->
        Log.error "These should've been removed already?!" 

  in
  let t, name_perms = strip_consumes env t in
  let names, perms = List.split name_perms in
  let names = Hml_List.filter_some names in
  let bindings = List.map (fun x -> x, KTerm) names in
  t, bindings, perms
;;


let rec translate_type (env: env) (t: typ): T.typ =
  match t with
  | TyLocated (t, p1, p2) ->
      translate_type (locate env p1 p2) t

  | TyTuple ts ->
      T.TyTuple (List.map (translate_type env) ts)

  | TyUnknown ->
      T.TyUnknown

  | TyDynamic ->
      T.TyDynamic

  | TyEmpty ->
      T.TyEmpty

  | TyVar x ->
      let _, index = find x env in
      T.TyVar index

  | TyConcreteUnfolded branch ->
      T.TyConcreteUnfolded (translate_data_type_def_branch env branch)

  | TySingleton t ->
      T.TySingleton (translate_type env t)

  | TyApp (t1, t2) ->
      T.TyApp (translate_type env t1, translate_type env t2)

  | TyArrow (t1, t2) ->
      (* Get the keys of a [Patricia.Map]. *)
      let keys =
        fun m -> List.rev (M.fold (fun k _v acc -> k :: acc) m [])
      in

      (* Get the implicitly quantified variables in [t1]. These will be
         quantified as universal variables above the arrow type. *)
      let t1_bindings = names t1 in
      let t1_bindings = keys t1_bindings in
      let t1_bindings = List.map (fun x -> (x, KTerm)) t1_bindings in

      (* This is the procedure that removes the consumes annotations. It is
       * performed in the surface syntax. The first step consists in carving out
       * the [consumes] annotations, replacing them with [=c]. *)
      let t1, perm_bindings, perms = strip_consumes env t1 in

      (* Now we give a name to [t1] so that we can speak about the argument in
       * the returned type. Note: this variable name is not lexable, so no risk
       * of conflict. *)
      let root, root_binding, t1 =
        match tunloc t1 with
        | TyNameIntro (x, t) ->
            x, [], t
        | _ ->
            let root = Variable.register (fresh_name "/root") in
            let root_binding = root, KTerm in
            root, [root_binding], t1
      in

      (* We now turn the argument into (=root | root @ t1 ∗ c @ … ∗ …) with [t1]
       * now devoid of any consumes annotations. *)
      let fat_t1 = TyBar (
        ty_equals root,
        fold_star (TyAnchoredPermission (TyVar root, t1) :: perms)
      ) in

      (* So that we don't mess up, we use unique names in the surface syntax and
       * let the translation phase do the proper index computations. *)
      let universal_bindings = t1_bindings @ perm_bindings @ root_binding in
      let env = List.fold_left bind env universal_bindings in
      let fat_t1 = translate_type env fat_t1 in

      (* The return type can also bind variables with [x: t]. These are
       * existentially quantified. *)
      let t2_bindings = names t2 in
      let t2_bindings = keys t2_bindings in
      let t2_bindings = List.map (fun x -> (x, KTerm)) t2_bindings in

      (* We need to return the original permission on [t1], minus the components
       * that were consumed: these have been carved out of [t1] by
       * [strip_consumes]. *)
      let t2 = TyBar (
        t2,
        TyAnchoredPermission (TyVar root, t1)
      ) in
      let env = List.fold_left bind env t2_bindings in

      (* Build the resulting type. *)
      let t2 = translate_type env t2 in
      let t2 = fold_exists t2_bindings t2 in
      let arrow = T.TyArrow (fat_t1, t2) in
      fold_forall universal_bindings arrow

  | TyForall (binding, t) ->
      let env = bind env binding in
      T.TyForall (binding, translate_type env t)

  | TyAnchoredPermission (t1, t2) ->
      T.TyAnchoredPermission (translate_type env t1, translate_type env t2)

  | TyStar (t1, t2) ->
      T.TyStar (translate_type env t1, translate_type env t2)

  | TyNameIntro (x, t) ->
      (* [x: t] translates into [(=x | x@t)] -- with [x] bound somewhere above
         us. *)
      let _, index = find x env in
      T.TyBar (
        T.TySingleton (T.TyVar index),
        T.TyAnchoredPermission (T.TyVar index, translate_type env t)
      )

  | TyConsumes _ ->
      (* These should've been removed by [strip_consumes]. *)
      illegal_consumes env

  | TyBar (t1, t2) ->
      T.TyBar (translate_type env t1, translate_type env t2)


and translate_data_type_def_branch (env: env) (branch: data_type_def_branch): T.data_type_def_branch =
  let datacon, fields = branch in
  let fields = List.map (function
    | FieldValue (name, t) ->
        T.FieldValue (name, translate_type env t)
    | FieldPermission t ->
        T.FieldPermission (translate_type env t)
  ) fields in
  datacon, fields
;;


let translate_abstract_fact (params: Variable.name list) (fact: abstract_fact option): T.fact =
  match fact with
  | None ->
      T.Affine
  | Some (FExclusive _) ->
      T.Exclusive
  | Some (FDuplicableIf (ts, _)) ->
      (* [KindCheck] already made sure these are just names _and_ they're valid. *)
      let names = List.map (function TyVar name -> name | _ -> assert false) ts in
      let arity = List.length params in
      let bitmap = Array.make arity false in
      List.iter (fun name ->
        let i = Hml_List.index name params in
        bitmap.(i) <- true
      ) names;
      T.Duplicable bitmap
;;

let translate_data_type_def (env: env) (data_type_def: data_type_def) =
  match data_type_def with
  | Concrete (flag, (name, params), branches) ->
      (* Add the type parameters in the environment. *)
      let env = List.fold_left bind env params in
      (* Translate! *)
      let branches = List.map (translate_data_type_def_branch env) branches in
      (* This fact will be refined later on. *)
      let arity = List.length params in
      let fact = match flag with
        | Exclusive -> T.Exclusive
        | Duplicable -> T.Duplicable (Array.make arity false)
      in
      name, Some (flag, branches), fact, karrow params KType
  | Abstract ((name, params), kind, fact) ->
      let fact = translate_abstract_fact (fst (List.split params)) fact in
      name, None, fact, karrow params kind
;;


(* [translate_data_type_group env tenv data_type_group] returns [env, tenv, points] where:
  - the type definitions have been added with the corresponding levels in [env]
  - type definitions have been desugared and added to [tenv]; the types have been
    opened inside the branches,
  - the points corresponding to the various types are in [points]; the item at
    index i has level i (the list is in order)
*)
let translate_data_type_group
    (env: env)
    (tenv: T.env)
    (data_type_group: data_type_group): env * T.env * T.point list
  =

  let bindings = bindings_data_type_group data_type_group in

  (* We're recycling the environments from [SurfaceSyntax] because we're lazy.
   * We don't really need the kind information here, but all the other functions
   * such as [bind] and [find] are defined already. *)
  let env = List.fold_left (bind ~strict:()) env bindings in 

  (* First do the translation pass. *)
  let translated_definitions: (Variable.name * T.type_def * T.fact * T.kind) list =
    List.map (translate_data_type_def env) data_type_group
  in

  (* Then build up the resulting environment. *)
  let tenv, points = List.fold_left (fun (tenv, acc) (name, def, fact, kind) ->
    let tenv, point = T.bind_type tenv name ?definition:def fact kind in
    tenv, point :: acc) (tenv, []
  ) translated_definitions in
  let points = List.rev points in

  (* Construct the reverse-map from constructors to points. *)
  let tenv = List.fold_left2 (fun tenv (_, def, _, _) point ->
    match def with
    | None ->
        tenv
    | Some (_, def) ->
        let type_for_datacon = List.fold_left (fun type_for_datacon (name, _) ->
          T.DataconMap.add name point type_for_datacon
        ) tenv.T.type_for_datacon def in  
        { tenv with T.type_for_datacon }
  ) tenv translated_definitions points in

  (* Finally, open the types in the type definitions themselves. *)
  let total_number_of_data_types = List.length points in
  let tenv = T.fold_types tenv (fun tenv point { T.kind; _ } { T.definition; _ } ->
    match definition with
    | None ->
        (* It's an abstract type, it has no branches that should be replaced. *)
        tenv

    | Some (flag, branches) ->
        let arity = T.get_arity_for_kind kind in

        (* Replace each TyVar with the corresponding TyPoint, for all branches. *)
        let branches = Hml_List.fold_lefti (fun level branches point ->
          (* We need to add [arity] because one has to move up through the type
           * parameters to reach the typed defined at [level]. *)
          let index = total_number_of_data_types - level - 1 + arity in
          (* Perform the substitution. *)
          List.map
            (T.tsubst_data_type_def_branch (T.TyPoint point) index)
            branches
        ) branches points in

        (* And replace the corresponding definition in [tenv]. *)
        T.replace_type tenv point (fun binder ->
          { binder with T.definition = Some (flag, branches) }
        )
  ) tenv in

  (* Return both environments and the list of points. *)
  env, tenv, points
;;


let open_type_definitions (points: T.point list) (declarations: E.declaration_group) =
  let total_number_of_data_types = List.length points in
  let subst_decl = fun declarations ->
    Hml_List.fold_lefti (fun level declarations point ->
      let index = total_number_of_data_types - level - 1 in
      E.tsubst_decl (T.TyPoint point) index declarations
    ) declarations points
  in
  subst_decl declarations
;;


let translate_declaration_group _ _ =
  []
;;


(* [translate env program] returns [env, decls] where:
  - type definitions from [program] have been added to the table of type
    definitions in [env] _and_ opened in both the type definitions themselves
    and [decls], which means all references to these types through [TyVar]s have
    been replaced by [TyPoint]s
  - [decls] is the desugared version of the original declarations; type
    definitions have been opened in there as well.
*)
let translate (tenv: T.env) (program: program): T.env * E.declaration_group =
  (* TEMPORARY we should probably accept an [env] here so that we can safely
   * compose this operation accross files... *)
  let data_type_group, declaration_group = program in
  (* This will just desugar the data type definitions, fill [tenv] with the
   * desugared definitions, an return a list of [points] so that we can
   * perform the substitution in the expressions once we've desugared them. *)
  let env, tenv, points = translate_data_type_group empty tenv data_type_group in
  (* Desugar the definitions. *)
  let declarations = translate_declaration_group env declaration_group in
  (* Perform the required substitutions. *)
  let declarations = open_type_definitions points declarations in
  (* And return everything. *)
  tenv, declarations
;;
