open Types

module TyCon = struct
  (* The name is here for printing purposes only. The “real” information is
   * contained in the global index. *)
  type t = Variable.name * index
  let compare = fun (_, x) (_, y) -> compare x y
  let show (name, _) = Variable.print name
end

module MD = ModeDeduction.Make(Mode)(TyCon)

open MD

(* This is what we return *)
type facts = rule list

(* When constraining type parameters, we know that:
   - the data type τ is either marked as exclusive, and then we have no
   constraints on its parameters
   - or τ is marked as duplicable, and then some of its parameters are
   duplicable; those are in the [bitmap] *)
type state = Exclusive | Duplicable of bitmap | Affine

(* This maps De Bruijn indices (inside a given type) to () if the parameter with
 * that index has to be duplicable, nothing otherwise. *)
and bitmap = unit IndexMap.t

(* Our internal working environment. *)
type env = {
  (* Maps global *levels* to knowledge we have acquired so far: the variable
   * name, for debugging; its arity; the corresponding bitfield, if any. *)
  types: (Variable.name * int * state) IndexMap.t;

  (* The current De Bruijn level. *)
  level: index;
}

(* [state env i] returns the associated state of the data type with De Bruijn
   *index* i, with respect to the current context env. *)
let state { level; types } i =
  try
    let _, _, state = IndexMap.find (level - i) types in
    state
  with Not_found ->
    (* TEMPORARY remove this debug information once everything works fine. *)
    IndexMap.iter (fun k (name, arity, _state) ->
      Log.debug "%d: %a[%d]" k Printers.p_var name arity
    ) types;
    Log.debug "Wanted: %d, level = %d" i level;
    assert false

(* A small helper function. *)
let flatten_tyapp t =
  let rec flatten_tyapp acc = function
    | TyApp (t1, t2) ->
        flatten_tyapp (t2 :: acc) t1
    | _ as x ->
        x, List.rev acc
  in
  flatten_tyapp [] t

exception NotDuplicable of typ
(* TEMPORARY this one will have to go eventually *)
exception NotSupported of string

(* Perform a reverse-analysis of a type, and return a bitmap of all indexes that
 * must be marked as duplicable for the original type to be duplicable itself. *)
let rev_duplicables
    (env: env)
    (t: typ)
    (map: bitmap) : bitmap =
  let rec rev_duplicables (map: bitmap) (t: typ) : bitmap =
    match t with
    | TyUnknown
    | TyDynamic ->
        map

    | TyVar i ->
        (* TEMPORARY this only works because we're not going through any binders
         * inside the type definition. The treatment of De Bruijn indexes is
         * definitely less than satisfactory... *)
        Log.debug "Duplicable: %d" i;
        IndexMap.add i () map
        
    (* Is this the correct behavior? We assume we only have ∀ followed by a
     * function type, which is always duplicable... and that we don't run into ∃
     * at all. *)
    | TyForall _
    | TyExists _ ->
        map

    | TyApp _ as t ->
      begin
        let hd, ts = flatten_tyapp t in
        let arity = List.length ts in
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
                Hml_List.fold_lefti (fun i map ti ->
                  let index = arity - i in
                  match IndexMap.find_opt index hd_bitmap with
                  | Some () ->
                      rev_duplicables map ti
                  | None ->
                      map
                ) map ts
          end
        | _ ->
            raise (NotSupported "Sorry, we don't allow Fω yet, all parameters must have ground kinds.")
      end


    | TyTuple ts ->
        List.fold_left (fun map -> function
          | TyTupleComponentValue t -> rev_duplicables map t
          | TyTupleComponentPermission _ ->
              (* TEMPORARY do something sensible in that case too *)
              assert false
        ) map ts

    (* TEMPORARY: for now on, let's say we're not dealing with these. In the
     * future, we'll have to match these to the correct data type, figure out what
     * its parameters are, and then proceed just like with TyApp. *)
    | TyConcreteUnfolded _ ->
        assert false

    (* Singleton types are always duplicable. *)
    | TySingleton _ ->
        map

    (* Arrows are always duplicable *)
    | TyArrow _ ->
        map

    (* TEMPORARY This doesn't really count, does it? *)
    | TyAnchoredPermission _
    | TyEmpty
    | TyStar _ ->
        assert false
  in
  rev_duplicables map t

(* This creates the environment in its initial state, and transforms the
 * knowledge we have gathered on the data types into a form that's suitable
 * for our analysis. *)
let create_and_populate_env (type_env: Types.env) : env =
  let n_cons = IndexMap.cardinal type_env.data_type_map in
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
  ) type_env.data_type_map { types = IndexMap.empty; level = n_cons } in
  env

(* Because inside the types, we're using De Bruijn indexes, the bitmaps are
 * reversed compared to the type declaration [data p1 p2 ...]. We flip them for
 * display purposes. *)
let string_of_bitmap bitmap max =
  String.concat "" (Hml_List.make max (fun i ->
    match IndexMap.find_opt (max - i) bitmap with Some () -> "x" | None -> "-"))

(* For debugging purposes. *)
let print_bitmap bitmap max =
  Log.debug "%s" (string_of_bitmap bitmap max)

(* For debugging purposes. *)
let print_env (env: env) : unit =
  let open Printers in
  IndexMap.iter (fun index (name, arity, state) ->
    match state with
    | Duplicable bitmap ->
        let bits = string_of_bitmap bitmap arity in
        Log.debug "%d: %a [%s]" index p_var name bits
    | Exclusive ->
        Log.debug "%d: %a [%s]" index p_var name "exclusive"
    | Affine ->
        Log.debug "%d: %a [%s]" index p_var name "affine"
  ) env.types

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
        let base_level = env.level in
        (* The type is in De Bruijn, so keep track of how many binders we've
         * crossed to get inside the type. *)
        let env = { env with level = base_level + arity } in
        let new_mode =
          try
            (* For each field, find out which parameters should be duplicable
             * for that field's type to be duplicable; merge them with the
             * current environment. *)
            let bitmap = List.fold_left (fun map (_name, fields) ->
                List.fold_left (fun map -> function
                  | FieldValue (_name, typ) ->
                      rev_duplicables env typ map
                  | FieldPermission _typ ->
                      (* TEMPORARY do something here too *)
                      assert false
                ) map fields
              ) bitmap branches in
            Duplicable bitmap
          with NotDuplicable _ ->
            (* Some exception was raised: we hit a type that's [Exclusive] or
             * [Affine], so the whole type need to be affine... *)
            Affine
        in
        let new_state = name, arity, new_mode in
        let env = {
          types = IndexMap.add level new_state env.types;
          level = base_level (* back at the base level *)
        } in
        env

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
