open WellKindedness
open Types
open Env

(* ------------------------------------------------------------------------- *)

(* The core of the algorithm. *)

exception NotDuplicable of typ
(* TEMPORARY this one will have to go eventually *)
exception NotSupported of string

(* The algorithm below can be used in two distinct phases. The first one
 * analyses a given data type definition, so the algorithm is allowed to request
 * that a parameter be duplicable for the whole type to be duplicable. The
 * second one tries to tell whether a given type is duplicable or not later on.
 * *)
type phase = Elaborating of level | Checking

(* This function performs a reverse-analysis of a type. As it goes, it marks
 * those variables that needs to be duplicable by updating [program_env]'s
 * [fact_for_type], using the [phase] parameter so that it knows which data
 * type it currently is analyzing. *)
let rev_duplicables
    (program_env: program_env)
    (working_env: working_env) 
    (phase: phase)
    (t: typ): program_env =
  let rec rev_duplicables (program_env: program_env) (working_env: working_env) (t: typ): program_env =
    match t with
    | TyUnknown
    | TyDynamic ->
        program_env

    | TyVar i ->
        let level = working_env.tlevel - i in
        Log.debug "TyVar index=%d, level=%d, tlevel=%d" i level working_env.tlevel;
        (* Is this a top-level data type? Type applications are flattened, so
         * this has to be referring to a top-level data type that has no
         * parameters, otherwise it's an error. *)
        begin
          match LevelMap.find_opt level program_env.fact_for_type with
          | Some Exclusive | Some Affine ->
              raise (NotDuplicable t)
          | Some (Duplicable _) ->
              if arity_for_data_type program_env level = 0 then
                program_env
              else
                Log.error "Partial type applications are not allowed"
          | None ->
            (* Now, is this a variable that's bound in the environment? When
             * checking, all variables must be bound. When elaborating, the type
             * parameters are not bound, because we're marking them as duplicable
             * or not in the environment. *)
            begin
              match LevelMap.find_opt level working_env.fact_for_var with
              | Some VExclusive | Some VAffine ->
                  raise (NotDuplicable t)
              | Some VDuplicable ->
                  program_env
              | None ->
                (* Now we have to be elaborating: we have to mark the type
                 * parameter as having to be duplicable in the [program_env]. *)
                begin
                  match phase with
                  | Elaborating my_level ->
                      Log.debug "↳ marking";
                      (* Levels in the interval [n, n + myarity[ are those for the
                       * current type's parameters. *)
                      let my_arity = arity_for_data_type program_env my_level in
                      let n = total_number_of_data_types program_env in
                      Log.affirm
                        (n <= level && level < n + my_arity)
                        "Referring to a type variable that's not in the right range";
                      (* I'm running out of indentation levels. *)
                      begin
                        match fact_for_type program_env my_level with
                        | Affine | Exclusive ->
                            Log.error "If we're marked as [Affine], someone\
                              threw [NotDuplicable], so we shouldn't even be here.\
                              If we're [Exclusive], we shouldn't even be here in\
                              the first place."
                        | Duplicable my_bitmap ->
                            Log.debug "↳ added level %d to my_bitmap my_level=%d tlevel=%d" level my_level working_env.tlevel;
                            let my_bitmap =
                              LevelMap.add level () my_bitmap
                            in
                            let fact_for_type =
                              LevelMap.add my_level (Duplicable my_bitmap) program_env.fact_for_type
                            in
                            { program_env with fact_for_type }
                      end
                  | Checking ->
                      Log.error "Unbound type variable at level %d" level
                end
              end
          end

    | TyFlexible _ ->
      begin
        match phase with
        | Elaborating _ ->
            Log.error "No flexible variables should appear at that stage"
        | Checking ->
            raise (NotSupported "I don't know how to analyze flexible variables yet, sorry")
      end

    | TyForall ((name, kind), t)
    | TyExists ((name, kind), t) ->
        let sub_working_env = bind_type working_env name in
        rev_duplicables program_env sub_working_env t

    | TyApp _ as t ->
      begin
        let cons, args = flatten_tyapp t in
        match cons with
        | TyVar index ->
          begin
            let level = working_env.tlevel - index in
            Log.debug "Applying %s (level=%d, bitmap=%a, tlevel=%d)"
              (name_for_type working_env level) level
              EnvPrinter.pdoc (TypePrinter.print_fact, (program_env, level))
              working_env.tlevel;
            match fact_for_type program_env level with
            | Exclusive | Affine ->
                raise (NotDuplicable t)
            | Duplicable cons_bitmap ->
                let n = total_number_of_data_types program_env in
                (* For each argument of the type application... *)
                Hml_List.fold_lefti (fun i program_env ti ->
                  (* The type at [level] may request its [i]-th parameter to be
                   * duplicable. *)
                  let param_level = n + i in
                  (match ti with | TyVar i -> Log.debug "• ti is TyVar %d" i; | _ -> ());
                  match LevelMap.find_opt param_level cons_bitmap with
                  | Some () ->
                      Log.debug "parameter %d HAS to be duplicable" i;
                      (* The answer is yes: the [i]-th parameter for the type
                       * application is [ti] and it has to be duplicable for the
                       * type at [level] to be duplicable too. *)
                      rev_duplicables program_env working_env ti
                  | None ->
                      Log.debug "parameter %d does NOT have to be duplicable" i;
                      (* The answer is no: there are no constraints on [ti]. *)
                      program_env
                ) program_env args
          end
        | _ ->
            Log.error "The head of a type application should be a type variable"
      end

    | TyTuple ts ->
        List.fold_left (fun program_env -> function
          | TyTupleComponentValue t
          | TyTupleComponentPermission t ->
              (* For a permission to be duplicable, the underlying type has to
               * be duplicable too. *)
              rev_duplicables program_env working_env t
        ) program_env ts

    | TyConcreteUnfolded (datacon, fields) as t ->
      begin
        let level = DataconMap.find datacon program_env.type_for_datacon in
        match LevelMap.find level program_env.def_for_type with
        | Concrete (flag, _, _, _) ->
          begin
            match flag with
            | SurfaceSyntax.Duplicable ->
                List.fold_left (fun env -> function
                  | FieldValue (_, typ)
                  | FieldPermission typ ->
                      rev_duplicables program_env working_env typ
                ) program_env fields
            | SurfaceSyntax.Exclusive ->
                raise (NotDuplicable t)
          end
        | Abstract _ ->
            assert false
      end

    | TySingleton _ ->
        (* Singleton types are always duplicable. *)
        program_env

    | TyArrow _ ->
        (* Arrows are always duplicable *)
        program_env

    | TyAnchoredPermission (x, t) ->
        (* That shouldn't be an issue, since x is probably TySingleton *)
        let program_env = rev_duplicables program_env working_env x in
        (* For x: τ to be duplicable, τ has to be duplicable as well *)
        rev_duplicables program_env working_env t
    | TyEmpty ->
        program_env
    | TyStar (p, q) ->
        (* For p ∗ q  to be duplicable, both p and q have to be duplicable. *)
        let program_env = rev_duplicables program_env working_env p in
        rev_duplicables program_env working_env q
  in
  rev_duplicables program_env working_env t
;;

(* This just fills in [program_env] with a “duplicable-unless-otherwise-specified”
 * semantics that is meant to evolve once we start running the algorithm. *)
let populate_env (program_env: program_env): program_env =
  LevelMap.fold (fun level def program_env ->
    match def with
    | Concrete (flag, _name, _kind, _branches) ->
      begin
        let fact =
          match flag with
          | SurfaceSyntax.Exclusive ->
              Exclusive
          | SurfaceSyntax.Duplicable ->
              Duplicable LevelMap.empty
        in
        { program_env with
          fact_for_type = LevelMap.add level fact program_env.fact_for_type
        }
      end
    | Abstract (name, _kind) ->
        (* In the absence of exported facts, we are conservative, and assume
         * that an abstract type is affine. Of course, later on, we might want
         * to inject here the assumptions revealed by, say, a module signature.
         * *)
        { program_env with
          fact_for_type = LevelMap.add level Affine program_env.fact_for_type
        }

  ) program_env.def_for_type program_env
;;

(* This performs one round of constraint propagation.
   - If the type is initially marked as Exclusive, it remains Exclusive.
   - If the type is marked as Duplicable, we recursively determine which ones of
   its type variables should be marked as duplicable for the whole type to be
   duplicable. *)
let one_round (program_env: program_env) (working_env: working_env): program_env =
  (* Folding on all the data types. *)
  LevelMap.fold (fun level fact program_env ->
    let phase = Elaborating level in
    (* What knowledge do we have from the previous round? *)
    match fact with
    | Exclusive | Affine ->
        (* This fact cannot evolve anymore, pass the [program_env] through. *)
        program_env
    | Duplicable bitmap ->
        let branches = branches_for_type program_env level in
        let arity = arity_for_data_type program_env level in
        let working_env = { working_env with tlevel = working_env.tlevel + arity } in
        try
          (* Folding on the branches. *)
          List.fold_left (fun program_env (_label, fields) ->
            (* Folding on the fields. *)
            List.fold_left (fun program_env -> function
              | FieldValue (_, typ)
              | FieldPermission typ ->
                  rev_duplicables program_env working_env phase typ
            ) program_env fields
          ) program_env branches
        with NotDuplicable _t ->
          (* Some exception was raised: the type, although initially
           * duplicable, contains a sub-part whose type is [Exclusive] or
           * [Affine], so the whole type need to be affine. *)
          { program_env with
            fact_for_type = LevelMap.add level Affine program_env.fact_for_type
          }

  ) program_env.fact_for_type program_env
;;

let analyze_data_types
    (program_env: program_env)
    (working_env: working_env): program_env =
  (* In the initial environment, all the bitmaps are empty. *)
  let program_env = populate_env program_env in
  (* We could be even smarter and make the function return both a new env and a
   * boolean telling whether we udpated the maps or not, but that would require
   * threading some [was_modified] variable throughout all the code. Because
   * premature optimization is the root of all evil, let's leave it as is for
   * now. *)
  let rec run_to_fixpoint program_env =
    Bash.(Log.debug ~level:2 "%sOne round of fact analysis...%s" colors.blue colors.default);
    let new_program_env = one_round program_env working_env in
    for level = 0 to total_number_of_data_types program_env - 1 do
      Log.debug ~level:2
        "name %s level %d bitmap %a | bitmap %a"
        (name_for_type working_env level)
        level
        EnvPrinter.pdoc (TypePrinter.print_fact, (program_env, level))
        EnvPrinter.pdoc (TypePrinter.print_fact, (new_program_env, level));
    done;
    let states_equal = fun m1 m2 ->
      match m1, m2 with
      | Duplicable b1, Duplicable b2 ->
          LevelMap.equal (=) b1 b2
      | Exclusive, Exclusive | Affine, Affine ->
          true
      | _ ->
          false
    in
    if LevelMap.equal states_equal new_program_env.fact_for_type program_env.fact_for_type then
      new_program_env
    else
      run_to_fixpoint new_program_env
  in
  run_to_fixpoint program_env
;;
