open Types

(* ------------------------------------------------------------------------- *)

(* The core of the algorithm. *)

(* The [duplicables] function may throw either one of these two to indicate the
 * reason why the type it's currently analyzing is not duplicable. I'm not sure
 * the code always gives the most precise reason. *)
exception EAffine of typ
exception EExclusive of typ

(* TEMPORARY this one will have to go eventually *)
exception NotSupported of string

(* The algorithm below can be used in two distinct phases. The first one
 * analyses a given data type definition, so the algorithm is allowed to request
 * that a parameter be duplicable for the whole type to be duplicable. The
 * second one tries to tell whether a given type is duplicable or not later on.
 * *)
type phase = Elaborating of bitmap | Checking

(* This function performs a reverse-analysis of a type. As it goes, it marks
 * those variables that needs to be duplicable by updating the bitmap contained
 * in [phase]. It may throw [EAffine] if it turns out the type it's
 * currently analyzing is affine. *)
let duplicables
    (env: env) 
    (phase: phase)
    (t: typ): unit =
  let rec duplicables (env: env) (t: typ): unit =
    match t with
    | TyUnknown
    | TyDynamic ->
        ()

    | TyVar index ->
        Log.debug ~level:4 "TyVar index=%d" index;
        begin
          match fact_for_type env index with
          | Exclusive | Affine ->
              raise (EAffine t)
          | Duplicable bitmap ->
              if Array.length bitmap != 0 then
                Log.error "Partial type applications are not allowed"
          | Fuzzy ->
              (* Only the current type's parameters are marked as fuzzy. *)
              begin
                match phase with
                | Elaborating my_bitmap ->
                    (* Levels in the interval [n, n + myarity[ are those for the
                     * current type's parameters. *)
                    let my_arity = Array.length my_bitmap in
                    let param_number =
                      ByIndex.cardinal env.bindings - index - env.toplevel_size - 1
                    in
                    Log.debug ~level:4 "↳ marking parameter %d" param_number;
                    Log.affirm (param_number >= 0 && param_number < my_arity)
                      "Marking as duplicable a variable that's not in the right\
                      range!\ param_number = %d" param_number;
                    my_bitmap.(param_number) <- true
                | Checking ->
                    Log.error "No fuzzy variables should be present when checking."
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
        let env = bind_type env name Affine (Abstract (name, kind)) in
        duplicables env t

    | TyApp _ as t ->
      begin
        let cons, args = flatten_tyapp t in
        match cons with
        | TyVar index ->
          begin
            Log.debug ~level:4 "Applying %s (index=%d, bitmap=%a)"
              (name_for_type env index) index
              TypePrinter.pdoc (TypePrinter.print_fact, (env, index));
            match fact_for_type env index with
            | Fuzzy ->
                Log.error "I messed up my index computations. Oops!";
            | Exclusive | Affine ->
                raise (EAffine t)
            | Duplicable cons_bitmap ->
                Log.affirm (List.length args = Array.length cons_bitmap)
                  "Arity mismatch, [WellKindedness] should've checked that";
                (* For each argument of the type application... *)
                List.iteri (fun i ti ->
                  (match ti with | TyVar i -> Log.debug ~level:4 "• ti is TyVar %d" i; | _ -> ());
                  (* The type at [level] may request its [i]-th parameter to be
                   * duplicable. *)
                  if cons_bitmap.(i) then begin
                      Log.debug ~level:4 "parameter %d HAS to be duplicable" i;
                      (* The answer is yes: the [i]-th parameter for the type
                       * application is [ti] and it has to be duplicable for the
                       * type at [level] to be duplicable too. *)
                      duplicables env ti
                  end else begin
                      Log.debug ~level:4 "parameter %d does NOT have to be duplicable" i
                      (* The answer is no: there are no constraints on [ti]. *)
                  end
                ) args
          end
        | _ ->
            Log.error "The head of a type application should be a type variable"
      end

    | TyTuple ts ->
        List.iter (function
          | TyTupleComponentValue t
          | TyTupleComponentPermission t ->
              (* For a permission to be duplicable, the underlying type has to
               * be duplicable too. *)
              duplicables env t
        ) ts

    | TyConcreteUnfolded (datacon, fields) as t ->
      begin
        let flag, _, _, _ = def_for_datacon env datacon in
        begin
          match flag with
          | SurfaceSyntax.Duplicable ->
              List.iter (function
                | FieldValue (_, typ)
                | FieldPermission typ ->
                    duplicables env typ
              ) fields
          | SurfaceSyntax.Exclusive ->
              raise (EExclusive t)
        end
      end

    | TySingleton _ ->
        (* Singleton types are always duplicable. *)
        ()

    | TyArrow _ ->
        (* Arrows are always duplicable *)
        ()

    | TyAnchoredPermission (x, t) ->
        (* That shouldn't be an issue, since x is probably TySingleton *)
        duplicables env x;
        (* For x: τ to be duplicable, τ has to be duplicable as well *)
        duplicables env t

    | TyEmpty ->
        ()

    | TyStar (p, q) ->
        (* For p ∗ q  to be duplicable, both p and q have to be duplicable. *)
        duplicables env p;
        duplicables env q
  in
  duplicables env t
;;

(* This performs one round of constraint propagation.
   - If the type is initially marked as Exclusive, it remains Exclusive.
   - If the type is marked as Duplicable, we recursively determine which ones of
   its type variables should be marked as duplicable for the whole type to be
   duplicable. *)
let one_round (env: env): env =
  Log.affirm (env.toplevel_size = ByIndex.cardinal env.bindings) "Huh?";
  TypePrinter.(Log.debug ~level:4 "env:\n  %a" pdoc (print_binders, env));
  (* Folding on all the data types. *)
  fold_types env (fun index env tname { fact; definition } ->
    (* What knowledge do we have from the previous round? *)
    match definition with
    | Abstract _ ->
        env
    | _ ->
    match fact with
    | Fuzzy ->
        Log.error "I messed up my index computations. Oops!";
    | Exclusive | Affine ->
        (* This fact cannot evolve anymore, pass [env] through. *)
        env
    | Duplicable bitmap ->
        Log.debug ~level:4 "Attacking %s%s%s %i %a" Bash.colors.Bash.red
          (name_for_type env index) Bash.colors.Bash.default
          index Variable.p tname;
        (* [bitmap] is shared! *)
        let phase = Elaborating bitmap in
        let inner_env = bind_datacon_parameters env (kind_for_type env index) in
        TypePrinter.(Log.debug ~level:4 "inner_env:\n  %a" pdoc (print_binders, inner_env));
        let branches = branches_for_type env index in
        try
          (* Iterating on the branches. *)
          List.iter (fun (_label, fields) ->
            (* Iterating on the fields. *)
            List.iter (function
              | FieldValue (_, typ)
              | FieldPermission typ ->
                  duplicables inner_env phase typ
            ) fields
          ) branches;
          env
        with EAffine _t ->
          (* Some exception was raised: the type, although initially
           * duplicable, contains a sub-part whose type is [Exclusive] or
           * [Affine], so the whole type need to be affine. *)
          replace_type env index (fun entry -> { entry with fact = Affine })
  ) env
;;

let analyze_type (env: env) (t: typ): fact =
  try
    duplicables env Checking t;
    Duplicable [||]
  with
  | EExclusive t' when t = t' ->
      Exclusive
  | _ ->
      Affine
;;
    

let analyze_data_types (env: env): env =
  (* We could be even smarter and make the function return both a new env and a
   * boolean telling whether we udpated the maps or not, but that would require
   * threading some [was_modified] variable throughout all the code. Because
   * premature optimization is the root of all evil, let's leave it as is for
   * now. *)
  let rec run_to_fixpoint env =
    Bash.(Log.debug ~level:2 "%sOne round of fact analysis...%s" colors.blue colors.default);
    let copy_fact = function
      | Duplicable bitmap ->
          Duplicable (Array.copy bitmap)
      | _ as x ->
          x
    in
    let old_facts = map_down_types env (fun _ { fact; _ } -> copy_fact fact) in
    let new_env = one_round env in
    let new_facts = map_down_types new_env (fun _ { fact; _ } -> copy_fact fact) in
    Hml_List.iter2i (fun level old_fact new_fact ->
      let index = ByIndex.cardinal env.bindings - level - 1 in
      Log.debug ~level:3
        "name %s\t index %d bitmap %a\t | bitmap %a"
        (name_for_type env index)
        index
        TypePrinter.pdoc (TypePrinter.do_print_fact, old_fact)
        TypePrinter.pdoc (TypePrinter.do_print_fact, new_fact);
    ) old_facts new_facts;
    if new_facts <> old_facts then
      run_to_fixpoint new_env
    else
      new_env
  in
  run_to_fixpoint env
;;
