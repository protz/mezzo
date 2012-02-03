(* This module implements a well-kindedness check for the types of
   the surface language. At the same time, types are translated
   down into the kernel language. *)

open SurfaceSyntax
module T = Types

(* ---------------------------------------------------------------------------- *)

(* Things we define for other modules *)

(** This environment contains information about all the types that have been
   defined in the global scope, and is used in the rest of the type-checking
   process.
    A data type defined in the global scope is assigned a “global De Bruijn
   index”. Therefore, all right-hand sides must be understood to be defined in
   that global environemnt, where all global names have been assigned indexes
   already. *)
type data_type_env = {
  (** Maps global levels to their meaning, i.e. a name for debugging, a kind,
     and a definition that has been converted to De Bruijn. *)
  data_type_map: data_type_entry T.LevelMap.t;
  (** Allows one to jump back from a constructor to the global index of its
     defining type. *)
  cons_map: T.index T.DataconMap.t;
}

and data_type_entry =
  | Concrete of SurfaceSyntax.data_type_flag * Variable.name * SurfaceSyntax.kind * T.data_type_def_branch list
  | Abstract of Variable.name * SurfaceSyntax.kind

(* ---------------------------------------------------------------------------- *)

(* Kind constructors. *)

let karrow bindings kind =
  List.fold_right (fun (x, kind1) kind2 ->
    KArrow (kind1, kind2)
  ) bindings kind

(* ---------------------------------------------------------------------------- *)

(* Error messages. *)

let unbound x =
  Log.error "Unbound type %a" Printers.p_var x

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
    kind, env.level - level
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
  | SurfaceSyntax.Abstract name ->
      (* All abstract types have [KType] for the time being. *)
      strict_add name KType tycons

let collect_data_type_group_tycon group : fragment =
  List.fold_left collect_data_type_def_tycon M.empty group

let rec check_data_type_group env (group: SurfaceSyntax.data_type_group) : data_type_env =
  (* Collect the names and kinds of the data types that are being
     defined. Check that they are distinct. Extend the environment. *)
  let env, _unordered_lhs = extend env (collect_data_type_group_tycon group) in
  (* TEMPORARY find a more meaningful name for that variable *)
  let infos = List.map (function
    | SurfaceSyntax.Concrete (flag, data_type_def_lhs, rhs) ->
        let name, _parameters = data_type_def_lhs in
        (* Check every data type definition. Get a [datacon * T.data_field_def list]
         * with the [data_field_def] in De Bruijn, of course. *)
        let rhs = check_data_type_def env (flag, data_type_def_lhs, rhs) in
        `Concrete (flag, name, rhs)
    | SurfaceSyntax.Abstract name ->
        `Abstract name
  ) group in
  (* Turn this into a viable environment that we can pass further down. *)
  make_type_env env infos

and make_type_env { mapping; _ } infos : data_type_env =
  let open T in
  let empty = {
    data_type_map = IndexMap.empty;
    cons_map = DataconMap.empty;
  } in
  List.fold_left (fun { data_type_map; cons_map; } info ->
    match info with
    | `Concrete (flag, var, branches) ->
        let kind, level = M.find var mapping in
        (* Log.debug "%a has level %d and its first datacon is %a"
          Printers.p_var var level
          Printers.p_con (fst (List.hd branches)); *)
        let cons_map = List.fold_left (fun cons_map (name, _) ->
          DataconMap.add name level cons_map
        ) cons_map branches in  
        let data_type_map =
          IndexMap.add level (Concrete (flag, var, kind, branches)) data_type_map
        in
        { cons_map; data_type_map }
    | `Abstract var ->
        let kind, level = M.find var mapping in
        let data_type_map = IndexMap.add level (Abstract (var, kind)) data_type_map in
        { cons_map; data_type_map }
  ) empty infos


(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module KindPrinter = struct

  open Printers
  open Types
  open TypePrinter

  (* Prints an abstract data type. Very straightforward. *)
  let print_abstract_type_def print_env name kind =
    string "data" ^^ space ^^ print_var name

  (* Prints a data type defined in the global scope. Assumes [print_env] has been
     properly populated. *)
  let print_data_type_def print_env flag name kind branches =
    let _return_kind, params = SurfaceSyntax.flatten_kind kind in
    (* Turn the list of parameters into letters *)
    let params: string list = name_gen (List.length params) in
    (* Add all these letters into the printing environment *)
    let print_env = List.fold_left (fun print_env param ->
      add param print_env) print_env params
    in
    (* Make these printable now *)
    let params = List.map print_string params in
    let sep = break1 ^^ bar ^^ space in
    let flag = match flag with
      | SurfaceSyntax.Exclusive -> string "exclusive" ^^ space
      | SurfaceSyntax.Duplicable -> empty
    in
    (* The whole blurb *)
    flag ^^ string "data" ^^ space ^^ lparen ^^
    print_var name ^^ space ^^ ccolon ^^ space ^^
    print_kind kind ^^ rparen ^^ join_left space params ^^
    space ^^ equals ^^
    jump
      (ifflat empty (bar ^^ space) ^^
      join sep (List.map (print_data_type_def_branch print_env) branches))

  (* This function prints the contents of a [Types.env]. *)
  let print_type_env env =
    (* Create an empty printing environment *)
    let print_env = { index = 0; names = IndexMap.empty; } in
    (* First, find out how many toplevel data types are defined in the current
     * environment. *)
    let n_cons = IndexMap.cardinal env.data_type_map in
    (* This small helper function registers all levels with their names in
     * the name map. *)
    let rec bind_datacon_names print_env =
      let { index; names } = print_env in
      if index = n_cons then
        print_env
      else begin
          (String.concat " " (List.map string_of_int (LevelMap.keys env.data_type_map)));
        match IndexMap.find index env.data_type_map with
        | Concrete (_, name, _, _)
        | Abstract (name, _) ->
            bind_datacon_names (add_var name print_env)
      end
    in
    let print_env = bind_datacon_names print_env in
    (* Now we have a pretty-printing environment that's ready, proceed. *)
    let defs = Hml_List.make n_cons (fun i ->
      match IndexMap.find i env.data_type_map with
      | Concrete (flag, name, kind, branches) ->
          print_data_type_def print_env flag name kind branches
      | Abstract (name, kind) ->
          print_abstract_type_def print_env name kind)
    in
    join (break1 ^^ break1) defs

  (* This function takes a [Types.env] and returns a string representation of it
     suitable for debugging / pretty-printing. *)
  let string_of_env e =
    let buf = Buffer.create 16 in
    let doc = print_type_env e in
    Pprint.PpBuffer.pretty 1.0 Bash.twidth buf doc;
    Buffer.contents buf
end
