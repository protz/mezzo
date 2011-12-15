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
   duplicable; those are in the [IndexMap] *)
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
        Log.debug "Duplicable: %d" i;
        IndexMap.add i () map
        
    (* Is this the correct behavior? We assume we only have ∀ followed by a
     * function type, which is always duplicable... and that we don't run into ∃ *)
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
                  match IndexMap.find_opt arity hd_bitmap with
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

(* Because inside the types, we're using De Bruijn indexes, the bitmap are
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
        Hml_String.beprintf "%d: %a [%s]\n" index p_var name bits
    | Exclusive ->
        Hml_String.beprintf "%d: %a [%s]\n" index p_var name "exclusive"
    | Affine ->
        Hml_String.beprintf "%d: %a [%s]\n" index p_var name "affine"
  ) env.types

let one_round (type_env: Types.env) (env: env) : env =
  IndexMap.fold (fun level (name, arity, state) env ->
    match state with
    | Exclusive | Affine ->
        env
    | Duplicable bitmap ->
        let _flag, _name, _kind, branches =
          IndexMap.find level type_env.data_type_map
        in
        Log.debug "Processing %a, arity %d" Printers.p_var name arity;
        let base_level = env.level in
        let env = { env with level = base_level + arity } in
        let new_mode =
          try
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
            Affine
        in
        let new_state = name, arity, new_mode in
        let env = {
          types = IndexMap.add level new_state env.types;
          level = base_level
        } in
        env

  ) env.types env



let analyze_data_types
    (type_env: Types.env)
    : facts =
  let env = create_and_populate_env type_env in
  print_env env;
  let env = one_round type_env env in
  print_env env;
  let env = one_round type_env env in
  print_env env;
  []

let string_of_facts facts =
  ""
