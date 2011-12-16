open Types

module TyCon = struct
  (* The name is here for printing purposes only. The “real” information is
   * contained in the global index. *)
  type t = Variable.name * index
  let compare = fun (_, x) (_, y) -> compare x y
  let show (name, _) = Variable.print name
end

module MD = ModeDeduction.Make(Mode)(TyCon)

(* This is what we return *)
type facts = MD.rule list


(* ------------------------------------------------------------------------- *)

(* Data structures for the fact inference algorithm. *)

(* Our internal working environment. This is all maps, and their keys are all De
 * Bruijn levels. When navigating inside a data type definition,
 * - the first few levels point to toplevel data type definitions: this is the
 *   [types] field;
 * - the following levels are for the current type's parameters: this is the
 *   [current] field – the first parameter of the type has the lowest level;
 * - all levels after that are for binders we've crossed, for instance a ∀
 *   quantifier: this is the [extra] field. *)
type env = {
  (* Maps global *levels* to knowledge we have acquired so far: the variable
   * name, for debugging; its arity; the corresponding bitfield, if any. *)
  types: (Variable.name * int * state) IndexMap.t;

  (* A bitfield, that maps De Bruijn levels to () if they have to be duplicable.
   * The integer is for the arity of the data type we're currently inspecting. *)
  current: int * bitmap;

  (* This is currently not very useful, but we'll probably need it once we start
   * allowing [foo: ∀(α::term).(duplicable α) => τ]. *)
  extra: var IndexMap.t;

  (* The current De Bruijn level. *)
  level: index;
}

(* When constraining type parameters, we know that:
   - the data type τ is either marked as exclusive or affine, and then we have
   no constraints on its parameters
   - or τ is marked as duplicable, and then some of its parameters are
   duplicable; those are in the [bitmap] *)
and state = Exclusive | Duplicable of bitmap | Affine

(* This maps levels of the current type parameters to () if that index has to be
 * duplicable, nothing otherwise. *)
and bitmap = unit IndexMap.t

(* The information we know about a variable bound inside a type, with ∀ for
 * instance. *)
and var = Variable.name


(* ------------------------------------------------------------------------- *)

(* Helper functions for working with environments and types. *)

exception NotDuplicable of typ
(* TEMPORARY this one will have to go eventually *)
exception NotSupported of string

(* [state env i] returns the associated state of the data type with De Bruijn
   *index* i, with respect to the current context env. *)
let state env i =
  try
    let level = env.level - i in
    let _, _, state = IndexMap.find level env.types in
    state
  with Not_found ->
    (* TEMPORARY remove this debug information once everything works fine.
     * NB: we're currently rejecting type parameters that don't have kind ∗.
     * Reaching this code would mean that the well-kindedness check failed. *)
    IndexMap.iter (fun k (name, arity, _state) ->
      Log.debug "%d: %a[%d]" k Printers.p_var name arity
    ) env.types;
    Log.debug "Wanted: %d, level = %d" i env.level;
    assert false

(* [mark_duplicable env i] returns a new environment where the type parameter
 * corresponding to De Bruijn index [i] has been marked as duplicable. *)
let mark_duplicable env i =
  let n_types = IndexMap.cardinal env.types in
  let level = env.level - i in
  let arity, bitmap = env.current in
  if not (level >= n_types && level < n_types + arity) then begin
    (* This means we're trying to mark as duplicable something that's not one of
       the type parameters.
       - It can't be a globally defined data type, because [data t = T { foo:
         list; }] is not well-kinded.
       - This means that it's one of the freshly introduced binders. *)
    match IndexMap.find_opt level env.extra with
    | Some _ ->
        (* Print some meaningful error message here, saying that _ is quantified
         * somehow and that we don't have the right hypothesis. *)
        raise (NotDuplicable (TyVar i))
    | None ->
        (* If we get there then I'm seriously wrong. *)
        assert false
  end;
  let bitmap = IndexMap.add level () bitmap in
  { env with current = arity, bitmap }

(* [ith_param_duplicable bitmap i] tells whether the i-th parameter of the type
 * whose bitmap is [bitmap] should be duplicable. *)
let ith_param_duplicable env bitmap i =
  let level = IndexMap.cardinal env.types + i in
  Option.unit_bool (IndexMap.find_opt level bitmap)

(* [add_binder env name] returns the new environment after we've entered an
 * extra binder whose name is [name] *)
let add_binder env name =
  let new_level = env.level + 1 in
  let extra = IndexMap.add new_level name env.extra in
  { env with level = new_level; extra }

(* A small helper function. *)
let flatten_tyapp t =
  let rec flatten_tyapp acc = function
    | TyApp (t1, t2) ->
        flatten_tyapp (t2 :: acc) t1
    | _ as x ->
        x, List.rev acc
  in
  flatten_tyapp [] t


(* ------------------------------------------------------------------------- *)

(* Some debugging / printing functions. *)

(* Give the global level of a type, get its state as a string. *)
let string_of_state env i =
  let _name, arity, state = IndexMap.find i env.types in
  let n_cons = IndexMap.cardinal env.types in
  match state with
  | Duplicable bitmap ->
      String.concat "" (Hml_List.make arity (fun i ->
        match IndexMap.find_opt (n_cons + i) bitmap with
        | Some () -> "x"
        | None -> "-")
      )
  | Exclusive ->
      "exclusive"
  | Affine ->
      "affine"

(* For debugging purposes. *)
let print_env (env: env) : unit =
  let open Printers in
  IndexMap.iter (fun index (name, arity, state) ->
    Log.debug "%d: %a [%s]" index p_var name (string_of_state env index);
    match state with
    | Duplicable bitmap ->
        Log.debug "  keys: %s" (String.concat ","
          (List.map string_of_int (IndexMap.keys bitmap)))
    | _ ->
        ()
  ) env.types


(* ------------------------------------------------------------------------- *)

(* The core of the algorithm. *)

(* Perform a reverse-analysis of a type, and return an env with the current
 * field set to a bitmap of all indexes that must be marked as duplicable for
 * the original type to be duplicable itself. *)
let rec rev_duplicables
    (env: env)
    (t: typ) : env =
  match t with
  | TyUnknown
  | TyDynamic ->
      env

  | TyVar i ->
      Log.debug "Duplicable: %d" i;
      mark_duplicable env i

  (* Is this the correct behavior? We assume we only have ∀ followed by a
   * function type, which is always duplicable... and that we don't run into ∃
   * at all. *)
  | TyForall _
  | TyExists _ ->
      env

  | TyApp _ as t ->
    begin
      let hd, ts = flatten_tyapp t in
      match hd with
      | TyVar i ->
        begin
          match state env i with
          | Exclusive | Affine ->
              raise (NotDuplicable t)
          | Duplicable hd_bitmap ->
              (* For each argument of the type application, if [hd] says that
               * its i-th argument has to be duplicable, then:
               * - find all type variables present in the argument that have
               * to be duplicable for the argument to be duplicable as well
               * - and add them to the map of variables so far.
               * Beware, the index in the list is not the De Bruijn index! The
               * bitmap keys are De Bruijn indexes. *)
              Hml_List.fold_lefti (fun i env ti ->
                if ith_param_duplicable env hd_bitmap i then
                  rev_duplicables env ti
                else
                  env
              ) env ts
        end
      | _ ->
          raise (NotSupported "Sorry, we don't allow Fω yet, you can only apply types to a globally defined data type.")
    end

  | TyTuple ts ->
      List.fold_left (fun env -> function
        | TyTupleComponentValue t ->
            rev_duplicables env t
        | TyTupleComponentPermission t ->
            (* For a permission to be duplicable, the underlying type has to be
             * duplicable too. *)
            rev_duplicables env t
      ) env ts

  (* TEMPORARY: for now on, let's say we're not dealing with these. In the
   * future, we'll have to match these to the correct data type, figure out what
   * its parameters are, and then proceed just like with TyApp. *)
  | TyConcreteUnfolded _ ->
      assert false

  (* Singleton types are always duplicable. *)
  | TySingleton _ ->
      env

  (* Arrows are always duplicable *)
  | TyArrow _ ->
      env

  (* TEMPORARY This doesn't really count, does it? *)
  | TyAnchoredPermission (x, t) ->
      (* That shouldn't be an issue, since x is probably TySingleton *)
      let env = rev_duplicables env x in
      (* For x: τ to be duplicable, τ has to be duplicable as well *)
      rev_duplicables env t
  | TyEmpty ->
      env
  | TyStar (p, q) ->
      (* For p ∗ q  to be duplicable, both p and q have to be duplicable. *)
      let env = rev_duplicables env p in
      rev_duplicables env q

(* This creates the environment in its initial state, and transforms the
 * knowledge we have gathered on the data types into a form that's suitable
 * for our analysis. *)
let create_and_populate_env (type_env: Types.env) : env =
  let n_cons = IndexMap.cardinal type_env.data_type_map in
  let empty = {
    types = IndexMap.empty;
    current = 0, IndexMap.empty;
    extra = IndexMap.empty;
    level = n_cons;
  } in
  let env = IndexMap.fold (fun i (flag, name, kind, _branches) env ->
    let _hd, kargs = SurfaceSyntax.flatten_kind kind in
    let arity = List.length kargs in
    match flag with
    | SurfaceSyntax.Exclusive ->
        { env with types =
          IndexMap.add i (name, arity, Exclusive) env.types }
    | SurfaceSyntax.Duplicable ->
        { env with types =
          IndexMap.add i (name, arity, (Duplicable IndexMap.empty)) env.types }
  ) type_env.data_type_map empty in
  env

(* This performs one round of constraint propagation.
   - If the type is initially marked as Exclusive, it remains Exclusive.
   - If the type is marked as Duplicable, we recursively determine which ones of
   its type variables should be marked as duplicable for the whole type to be
   duplicable. We first iterate on the branches, then on the fields inside the
   branches. *)
let one_round (type_env: Types.env) (env: env) : env =
  IndexMap.fold (fun level (name, arity, state) env ->
    (* The [level] variable is the global level of the data type we're currently
     * examining. *)
    match state with
    | Exclusive | Affine ->
        env
    | Duplicable bitmap ->
        (* TEMPORARY I wonder if we should put that in [env] and get rid of
         * [type_env]. *)
        let _flag, _name, _kind, branches =
          IndexMap.find level type_env.data_type_map
        in
        Log.debug "Processing %a, arity %d" Printers.p_var name arity;
        (* The type is in De Bruijn, so keep track of how many binders we've
         * crossed to get inside the type. *)
        let sub_env = {
          types = env.types;
          current = arity, bitmap;
          extra = IndexMap.empty;
          level = env.level + arity;
        } in
        let new_mode =
          try
            (* For each field, find out which parameters should be duplicable
             * for that field's type to be duplicable; merge them with the
             * current environment. *)
            let sub_env = List.fold_left (fun sub_env (_label, fields) ->
                List.fold_left (fun sub_env -> function
                  | FieldValue (_, typ)
                  | FieldPermission typ ->
                      rev_duplicables sub_env typ
                ) sub_env fields
              ) sub_env branches in
            Duplicable (snd sub_env.current)
          with NotDuplicable _t ->
            (* Some exception was raised: we hit a type that's [Exclusive] or
             * [Affine], so the whole type need to be affine... *)
            Affine
        in
        let new_state = name, arity, new_mode in
        { env with types = IndexMap.add level new_state env.types }

  ) env.types env

let analyze_data_types
    (type_env: Types.env)
    : facts =
  (* In the initial environment, all the bitmaps are empty. *)
  let env = create_and_populate_env type_env in
  (* We could be even smarter and make the function return both a new env and a
   * boolean telling whether we udpated the maps or not, but that would require
   * threading some [was_modified] variable throughout all the code. Because
   * premature optimization is the root of all evil, let's leave it as is for
   * now. *)
  let rec run_to_fixpoint env =
    Bash.(Log.debug "%sOne round...%s" colors.blue colors.default);
    let new_env = one_round type_env env in
    let states_equal = fun (_, _, m1) (_, _, m2) ->
      match m1, m2 with
      | Duplicable b1, Duplicable b2 ->
          IndexMap.equal (=) b1 b2
      | Exclusive, Exclusive | Affine, Affine ->
          true
      | _ ->
          false
    in
    if IndexMap.equal states_equal new_env.types env.types then
      new_env
    else
      run_to_fixpoint new_env
  in
  let env = run_to_fixpoint env in
  print_env env;
  []

let string_of_facts facts =
  ""
