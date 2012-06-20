(* This module translates the surface syntax down to our internal
   representation.

   - All implicit name bindings made through [TyNameIntro] are turned into
     explicit quantifiers, either [TyForAll] or [TyExists].
   - Function parameters that are not consumed, when desugared, generate a
     permission in the returned type. [TyConsumes] annotations are removed.
   - Type annotations in patterns are removed, and are attached to let or val
     bindings instead.
   - Location information inside types and patterns is dropped.
*)

open SurfaceSyntax
open KindCheck

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


let translate_type (_env: env) (_t: typ): T.typ =
  assert false
;;


let translate_data_type_branch (env: env) (branch: data_type_def_branch): T.data_type_def_branch =
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
      let branches = List.map (translate_data_type_branch env) branches in
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
  assert false
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
