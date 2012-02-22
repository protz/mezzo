(* This module implements a well-kindedness check for the types of
   the surface language. At the same time, types are translated
   down into the kernel language. *)

open SurfaceSyntax
module T = Types

(* ---------------------------------------------------------------------------- *)

(* Kind constructors. *)

let karrow bindings kind =
  List.fold_right (fun (x, kind1) kind2 ->
    KArrow (kind1, kind2)
  ) bindings kind

(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module KindPrinter = struct

  open Hml_Pprint
  open Types
  open TypePrinter

  (* Prints an abstract data type. Very straightforward. *)
  let print_abstract_type_def print_env name kind =
    string "abstract" ^^ space ^^ print_var name ^^ space ^^ ccolon ^^ space ^^
    print_kind kind
  ;;

  (* Prints a data type defined in the global scope. Assumes [print_env] has been
     properly populated. *)
  let print_data_type_def (env: env) flag name kind branches =
    let _return_kind, params = flatten_kind kind in
    (* Turn the list of parameters into letters *)
    let letters: string list = name_gen (List.length params) in
    let letters = List.map print_string letters in
    let env, branches = bind_datacon_parameters env kind branches in
    let sep = break1 ^^ bar ^^ space in
    let flag = match flag with
      | SurfaceSyntax.Exclusive -> string "exclusive" ^^ space
      | SurfaceSyntax.Duplicable -> empty
    in
    (* The whole blurb *)
    flag ^^ string "data" ^^ space ^^ lparen ^^
    print_var name ^^ space ^^ ccolon ^^ space ^^
    print_kind kind ^^ rparen ^^ join_left space letters ^^
    space ^^ equals ^^
    jump
      (ifflat empty (bar ^^ space) ^^
      join sep (List.map (print_data_type_def_branch env) branches))
  ;;

  (* This function prints the contents of a [Types.env]. *)
  let print_kinds env =
    (* Now we have a pretty-printing environment that's ready, proceed. *)
    let defs = map_types env (fun _ { definition; _ } ->
      match definition with
      | Concrete (flag, name, kind, branches) ->
          print_data_type_def env flag name kind branches
      | Abstract (name, kind) ->
          print_abstract_type_def env name kind
      | _ ->
          assert false)
    in
    join (break1 ^^ break1) defs
  ;;

  let print_kinds_and_facts program_env =
    string "KINDS:" ^^ nest 2 (hardline ^^ print_kinds program_env) ^^ hardline ^^
    hardline ^^
    string "FACTS:" ^^ nest 2 (hardline ^^ print_facts program_env) ^^ hardline
  ;;

end
(* ---------------------------------------------------------------------------- *)

(* Error messages. *)

let unbound x =
  Log.error "Unbound type %a" Variable.p x

let mismatch expected_kind inferred_kind =
  Log.error "This type has kind %a but we were expecting kind %a"
    T.TypePrinter.p_kind inferred_kind
    T.TypePrinter.p_kind expected_kind

let illegal_consumes () =
  assert false (* TEMPORARY *)

let illegal_named_tuple_component x =
  assert false (* TEMPORARY *)

let deconstruct_arrow = function
  | KArrow (ty1, ty2) ->
      ty1, ty2
  | kind ->
      assert false (* TEMPORARY *)

let bound_twice x =
  assert false (* TEMPORARY *)

(* ---------------------------------------------------------------------------- *)

(* Maps of identifiers to things. *)

module M =
  Variable.Map

let strict_add x kind env =
  try
    M.strict_add x kind env
  with M.Unchanged ->
    bound_twice x

(* ---------------------------------------------------------------------------- *)

(* An environment maps an identifier to a pair of a kind and a de Bruijn level
   (not to be confused with a de Bruijn index!). An environment also keeps
   track of the current de Bruijn level. *)

type level = 
    int

type env = {
  (* The current de Bruijn level. *)
  level: level;
  (* A mapping of identifiers to pairs of a kind and a level. *)
  mapping: (kind * level) M.t;
}

type fragment =
    kind M.t

(* The empty environment. *)

let empty : env =
  { level = 0; mapping = M.empty }

(* [find x env] looks up the name [x] in the environment [env] and returns a
   pair of a kind and a de Bruijn index (not a de Bruijn level!). *)

let find x env =
  try
    let kind, level = M.find x env.mapping in
    kind, env.level - level - 1
  with Not_found ->
    unbound x

(* [bind env (x, kind)] binds the name [x] with kind [kind]. *)

let bind env (x, kind) : env =
  (* The current level becomes [x]'s level. The current level is
     then incremented. *)
  { level = env.level + 1;
    mapping = M.add x (kind, env.level) env.mapping }

(* [extend env xs] extends the current environment with new bindings; [xs] is
   a fragment, that is, a map of identifiers to kinds. Because an arbitrary
   order is chosen for the bindings, the function returns not only an extended
   environment, but also a list of bindings, which indicates in which order
   the bindings are performed. At the head of the list comes the innermost
   binding. *)

let extend (env : env) (xs : fragment) : env * type_binding list =
  M.fold (fun x kind (env, bindings) ->
    let binding = (x, kind) in
    bind env binding,
    binding :: bindings
  ) xs (env, [])

(* [forall bindings ty] builds a series of universal quantifiers.
   The innermost binding comes first in the list [bindings]. *)

let forall bindings ty =
  List.fold_left (fun ty binding ->
    T.TyForall (binding, ty)
  ) ty bindings

(* [exist bindings ty] builds a series of existential quantifiers.
   The innermost binding comes first in the list [bindings]. *)

let exist bindings ty =
  List.fold_left (fun ty binding ->
    T.TyExists (binding, ty)
  ) ty bindings

(* ---------------------------------------------------------------------------- *)

(* [bi ty] produces a set of the identifiers that are brought into scope by
   the type [ty], when this type is found on the left-hand side of an arrow.
   In short, a tuple type can bind names for some or all of its components;
   any other type does not bind any names. *)

let rec bi ty : fragment =
  match ty with
  | TyTuple [ (ConsumesAndProduces, TyTupleComponentValue (None, ty)) ] ->
      (* A tuple of one anonymous component is interpreted as a pair
	 of parentheses. *)
      bi ty
  | TyTuple components ->
      (* A tuple type can bind names for some or all of its components. *)
      List.fold_left (fun env (_, component) ->
	match component with
	| TyTupleComponentValue (Some x, _) ->
	    (* These names must be distinct. *)
	    strict_add x KTerm env
	| TyTupleComponentValue (None, _)
	| TyTupleComponentPermission _ ->
	    env
      ) M.empty components
  | _ ->
      (* A non-tuple type does not bind any names. *)
      M.empty

(* ---------------------------------------------------------------------------- *)

(* [infer special env ty] and [check special env ty kind] perform bottom-up
   kind inference and kind checking. The flag [special] tells whether we are
   under the left-hand side of an arrow. When this flag is set, and only then,
   tuple types are treated differently: the [consumes] keyword is permitted,
   and names for components are ignored (because they have been bound already).
   The environment [env] maps variables to kinds. *)

(* [infer] and [check] also perform the translation down to the kernel
   language. [infer] returns a pair of a kind and a type, whereas [check]
   returns just a type. *)

let rec infer special env ty : kind * T.typ =
  match ty with
  | TyTuple [ (ConsumesAndProduces, TyTupleComponentValue (None, ty)) ] ->
      (* A tuple of one anonymous component is interpreted as a pair
	 of parentheses. This special case is important: without it,
         any type that is placed within parentheses would be viewed
	 as a tuple, hence it would be forced to have kind [KType]. *)
      infer special env ty
  | TyTuple components ->
      (* Normally, a tuple type binds names for its components. We
	 extract these names and build a new environment within
	 which the components are checked. However, if [special]
	 is set, then we have already extracted and bound these
	 names, so we must not do it again. *)
      KType,
      if special then
	T.TyTuple (List.flatten (List.map (check_tuple_type_component special env) components))
      else
	let env, bindings = extend env (bi ty) in
	exist bindings (
	  T.TyTuple (List.flatten (List.map (check_tuple_type_component special env) components))
	)
  | TyUnknown ->
      KType,
      T.TyUnknown
  | TyDynamic ->
      KType,
      T.TyDynamic
  | TyEmpty ->
      KPerm,
      T.TyEmpty
  | TyVar x ->
      let kind, index = find x env in
      kind,
      T.TyVar index
  | TyConcreteUnfolded (datacon, fields) ->
      (* TEMPORARY check that this is consistent with the definition of datacon *)
      KType,
      T.TyConcreteUnfolded (datacon, List.map (check_data_field_def env) fields)
  | TySingleton tyx ->
      KType,
      T.TySingleton (check false env tyx KTerm)
  | TyApp (ty1, ty2) ->
      let kind1, ty1 = infer false env ty1 in
      let domain, codomain = deconstruct_arrow kind1 in
      codomain,
      T.TyApp (
	ty1,
	check false env ty2 domain
      )
  | TyArrow (ty1, ty2) ->
      (* Gather the names bound by the left-hand side, if any. These names
	 are bound in the left-hand and right-hand sides. *)
      let env, bindings = extend env (bi ty1) in
      (* Check the left-hand and right-hand sides. *)
      KType,
      forall bindings (T.TyArrow (
	check true env ty1 KType,
	check false env ty2 KType
      ))
      (* TEMPORARY any components that are marked [ConsumesAndProduces]
	 in the left-hand side should be copied (as a permission only)
	 to the right-hand side; this requires generating a name if the
	 component is anonymous. I imagine it can be done as a source-to-source
	 transformation (on-the-fly, right here), but generating a fresh
	 identifier is somewhat tricky. Let me think about this later... *)
  | TyForall (binding, ty) ->
      let env = bind env binding in
      (* It seems that we can require the body of a universal type to
	 have type [KType]. Allowing [KTerm] does not make sense, and
	 allowing [KPerm] makes sense but does not sound useful in
	 practice. *)
      KType,
      forall [ binding ] (check false env ty KType)
  | TyAnchoredPermission (tyx, ty) ->
      KPerm,
      T.TyAnchoredPermission (
	check false env tyx KTerm,
	check false env ty KType
      )
  | TyStar (ty1, ty2) ->
      KPerm,
      T.TyStar (
	check false env ty1 KPerm,
	check false env ty2 KPerm
      )

and check special env ty expected_kind =
  let inferred_kind, ty = infer special env ty in
  if expected_kind = inferred_kind (* generic equality at kinds! *) then
    ty
  else
    mismatch expected_kind inferred_kind

(* The following function performs kind checking and translation for a tuple
   component. The component is expected to have kind [KType]. It can be
   translated into one or two components. *)

and check_tuple_type_component special env (annotation, component) : T.tuple_type_component list =
  (* Check that [consumes] is used only where meaningful, that is,
     only under the left-hand side of an arrow. *)
  if (annotation = Consumes) && (not special) then
    illegal_consumes ();
  (* TEMPORARY translate ConsumesAndProduces correctly! *)
  (* Check this tuple component. *)
  match component with
  | TyTupleComponentValue (Some x, ty) ->
      (* When translating a component named [x], the name [x] has
	 already been bound. Look up the index associated with [x],
	 and translate this component as two components: a value
	 component of singleton type [=x] and a permission component
	 of type [x: ty]. *)
      let (_ : kind), index = find x env in
      let var = T.TyVar index in
      [ T.TyTupleComponentValue (T.TySingleton var);
	T.TyTupleComponentPermission (T.TyAnchoredPermission (var, check false env ty KType)) ]
  | TyTupleComponentValue (None, ty) ->
      [ T.TyTupleComponentValue (check false env ty KType) ]
  | TyTupleComponentPermission ty ->
      [ T.TyTupleComponentPermission (check false env ty KPerm) ]

and check_data_field_def env = function
  | FieldValue (f, ty) ->
      (* Field names are preserved. *)
      T.FieldValue (f, check false env ty KType)
  | FieldPermission ty ->
      T.FieldPermission (check false env ty KPerm)

(* ---------------------------------------------------------------------------- *)

(* Kind checking for algebraic data type definitions. *)

let check_data_type_def_branch env (datacon, fields) =
  (* TEMPORARY should we allow dependencies? i.e. every field name could
     be bound within every field type. Think! *)
  (* TEMPORARY could also allow "this" to be bound *)
  (* TEMPORARY check that field names are pairwise distinct *)
  datacon,
  List.map (check_data_field_def env) fields

let check_data_type_def_rhs env rhs =
  (* TEMPORARY check that the datacons are pairwise distinct *)
  List.map (check_data_type_def_branch env) rhs

let collect_data_type_def_lhs_parameters env (tycon, bindings) : env =
  (* Do not bother checking that the parameters are distinct. *)
  List.fold_left bind env bindings

let check_data_type_def env (_flag, lhs, rhs) =
  check_data_type_def_rhs (collect_data_type_def_lhs_parameters env lhs) rhs

let collect_data_type_def_lhs_tycon tycons (tycon, bindings) : fragment =
  strict_add tycon (karrow bindings KType) tycons

let collect_data_type_def_tycon tycons (def: SurfaceSyntax.data_type_def) : fragment =
  match def with
  | SurfaceSyntax.Concrete (_flag, lhs, _) ->
      collect_data_type_def_lhs_tycon tycons lhs
  | SurfaceSyntax.Abstract (name, params, return_kind, fact) ->
      let kind = List.fold_right
        (fun (_name, kind) acc -> KArrow (kind, acc))
        params
        return_kind
      in
      strict_add name kind tycons

let collect_data_type_group_tycon group : fragment =
  List.fold_left collect_data_type_def_tycon M.empty group

let check_data_type_group (env: env) (group: SurfaceSyntax.data_type_group) : T.env =
  let open Types in
  (* Collect the names and kinds of the data types that are being
     defined. Check that they are distinct. Extend the environment. *)
  let env, bindings = extend env (collect_data_type_group_tycon group) in
  (* Fold over all the type definitions, and enrich the [type_env: Types.env]
   * with them as we go. *)
  let type_env, points = List.fold_left (fun (type_env, points) -> function
    | SurfaceSyntax.Concrete (flag, data_type_def_lhs, rhs) ->
        let name, parameters = data_type_def_lhs in
        let arity = List.length parameters in
        (* Check every data type definition. Get a [datacon * T.data_field_def list]
         * with the [data_field_def] in De Bruijn, of course. *)
        let rhs = check_data_type_def env (flag, data_type_def_lhs, rhs) in
        let kind, level = M.find name env.mapping in
        Log.debug ~level:4 "Level %d name %a" level Variable.p name;
        let fact = match flag with
          | SurfaceSyntax.Duplicable ->
              (* This fact is bound to evolve later on in [FactInference]. *)
              Duplicable (Array.make arity false)
          | SurfaceSyntax.Exclusive ->
              Exclusive
        in
        (* Keep the definition as we will need to refer to it later on. *)
        let type_env, point =
          bind_type type_env name fact (Concrete (flag, name, kind, rhs))
        in
        (* Map all the constructor names to the corresponding type. *)
        let type_for_datacon = List.fold_left (fun type_for_datacon (name, _) ->
          DataconMap.add name point type_for_datacon
        ) type_env.type_for_datacon rhs in  
        (* We keep the point corresponding to the level, so that we can, later
         * on, replace all bound variables in the data type definitions with the
         * corresponding [TyPoint]s. *)
        { type_env with type_for_datacon }, (level, point) :: points
    | SurfaceSyntax.Abstract (name, params, _return_kind, fact) ->
        let kind, level = M.find name env.mapping in
        Log.debug ~level:4 "Level %d name %a" level Variable.p name;
        (* We should probably move the part below into some sort of
         * [check_abstract_type_fact] function. *)
        let fact =
          (* The variables that appear in the fact are considered to be bound in
           * the abstract type declaration above. E.g. in
           *   abstract list a
           *   fact duplicable a => duplicable (list a)
           * a is bound on the first line. So add them all in the environment. *)
          let env =
            List.fold_left (fun env var -> bind env var) env params
          in
          (* Inspect the (original) AST fact *)
          match fact with
          | None ->
              Affine
          | Some (FExclusive _) ->
              Exclusive
          | Some (FDuplicableIf (components, _)) ->
              (* We collect the type variables that appear in the LHS of the
               * =>. *)
              let vars =
                let open SurfaceSyntax in
                List.map (function
                  | _, TyTupleComponentValue (None, TyVar name) ->
                      name
                  | _ ->
                      Log.error "We only support very simple facts."
                ) components
              in
              (* Get the levels of the type parameters that appear in the LHS of
               * the =>. *)
              let _kinds, indices = List.split (List.map (fun x -> find x env) vars) in
              (* Compute the arity of the type. *)
              let _hd, tl = flatten_kind kind in
              let arity = List.length tl in
              (* Turn this into "the i-th parameter has to be duplicable". *)
              let param_numbers = List.map (fun x -> arity - x - 1) indices in
              (* Create and modify the bitmap accordingly. This one won't evolve
               * anymore. *)
              let bitmap = Array.make arity false in
              List.iter (fun i -> bitmap.(i) <- true) param_numbers;
              (* TEMPORARY One thing we didn't check is the RHS of the =>. *)
              Duplicable bitmap
        in
        (* Just remember that the type is defined as abstract. *)
        let type_env, point = bind_type type_env name fact (Abstract (name, kind)) in
        type_env, (level, point) :: points
  ) (empty_env, []) group in
  (* Now substitute the TyVars for the TyPoints: for all definitions *)
  let total_number_of_data_types = List.length points in
  fold_types type_env (fun type_env point names { definition; _ } ->
    match definition with
    | Abstract _ ->
        type_env
    | Concrete (flag, name, kind, branches) ->
        let arity = arity_for_def definition in
        (* Replace each TyVar with the corresponding TyPoint *)
        let branches = List.fold_left (fun branches (level, point) ->
          let index = total_number_of_data_types - level - 1 + arity in
          List.map
            (subst_data_type_def_branch (TyPoint point) index)
            branches
        ) branches points in
        replace_type type_env point (fun binder ->
          { binder with definition = Concrete (flag, name, kind, branches) }
        )
    | _ ->
        assert false
  ) type_env
