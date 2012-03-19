(* This module implements a well-kindedness check for the types of
   the surface language. At the same time, types are translated
   down into the kernel language. *)

open SurfaceSyntax
module T = Types
module E = Expressions

(* ---------------------------------------------------------------------------- *)

(* Kind constructors. *)

let karrow bindings kind =
  List.fold_right (fun (x, kind1) kind2 ->
    KArrow (kind1, kind2)
  ) bindings kind

(* ---------------------------------------------------------------------------- *)

(* Maps of identifiers to things. *)

module M =
  Variable.Map

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
  (* The current start and end positions *)
  location: Lexing.position * Lexing.position;
}

(* The empty environment. *)

let empty : env =
  { level = 0; mapping = M.empty; location = Lexing.dummy_pos, Lexing.dummy_pos }

(* Error messages. *)

type error = env * raw_error

and raw_error =
  | Unbound of Variable.name
  | Mismatch of kind * kind
  | NotAnArrow of T.typ * kind
  | BoundTwice of Variable.name

exception WellKindednessError of error

let raise_error env e =
  raise (WellKindednessError (env, e))
;;

let print_error buf (env, raw_error) =
  let open T.TypePrinter in
  begin match raw_error with
  | Unbound x ->
      Printf.bprintf buf
        "%a unbound identifier %a"
        Lexer.p env.location
        Variable.p x
  | Mismatch (expected_kind, inferred_kind) ->
      Printf.bprintf buf
        "%a this type has kind %a but we were expecting kind %a"
        Lexer.p env.location
        p_kind inferred_kind
        p_kind expected_kind
  | NotAnArrow (t, kind) ->
      Printf.bprintf buf
        "%a cannot apply arguments to type %a since it has kind %a"
        Lexer.p env.location
        pdoc (ptype, (Types.empty_env, t))
        p_kind kind
  | BoundTwice x ->
      Printf.bprintf buf
        "%a variable %a is bound twice"
        Lexer.p env.location
        Variable.p x
  end;
  (* Uncomment this part to get a really verbose error message. *)
  (* Printf.bprintf buf "\n";
  let bindings = M.fold (fun x (kind, level) acc ->
    (level, (x, kind)) :: acc) env.mapping []
  in
  let bindings = List.sort (fun (x, _) (y, _) -> compare x y) bindings in
  List.iter (fun (level, (x, kind)) ->
    Printf.bprintf buf "At level %d, variable %a with kind=%a\n"
      level
      Variable.p x
      p_kind kind
  ) bindings; *)
;;

let unbound env x =
  raise_error env (Unbound x)

let mismatch env expected_kind inferred_kind =
  raise_error env (Mismatch (expected_kind, inferred_kind))

let illegal_consumes () =
  assert false (* TEMPORARY *)

let illegal_named_tuple_component x =
  assert false (* TEMPORARY *)

let deconstruct_arrow env t = function
  | KArrow (ty1, ty2) ->
      ty1, ty2
  | kind ->
      raise_error env (NotAnArrow (t, kind))

let bound_twice x =
  raise_error empty (BoundTwice x)

(* ---------------------------------------------------------------------------- *)

let strict_add x kind env =
  try
    M.strict_add x kind env
  with M.Unchanged ->
    bound_twice x

(* ---------------------------------------------------------------------------- *)

type fragment =
    kind M.t

(* [find x env] looks up the name [x] in the environment [env] and returns a
   pair of a kind and a de Bruijn index (not a de Bruijn level!). *)

let find x env =
  try
    let kind, level = M.find x env.mapping in
    kind, env.level - level - 1
  with Not_found ->
    unbound env x

(* [bind env (x, kind)] binds the name [x] with kind [kind]. *)

let bind env (x, kind) : env =
  (* The current level becomes [x]'s level. The current level is
     then incremented. *)
  { env with
    level = env.level + 1;
    mapping = M.add x (kind, env.level) env.mapping }

(* [locate env p1 p2] extends [env] with the provided location information. *)
let locate env p1 p2: env =
  { env with location = p1, p2 }

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
      let domain, codomain = deconstruct_arrow env ty1 kind1 in
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
    mismatch env expected_kind inferred_kind

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

let check_data_type_group
    (type_env: T.env)
    (env: env)
    (group: SurfaceSyntax.data_type_group): env * (level * T.point) list * T.env =
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
          bind_type type_env name ~definition:(flag, rhs) fact kind
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
        let type_env, point = bind_type type_env name fact kind in
        type_env, (level, point) :: points
  ) (type_env, []) group in
  (* Now substitute the TyVars for the TyPoints: for all definitions *)
  let total_number_of_data_types = List.length points in
  env, points, fold_types type_env (fun type_env point { names; kind } { definition; _ } ->
    match definition with
    | None ->
        type_env
    | Some (flag, branches) ->
        let arity = get_arity_for_kind kind in
        (* Replace each TyVar with the corresponding TyPoint *)
        let branches = List.fold_left (fun branches (level, point) ->
          let index = total_number_of_data_types - level - 1 + arity in
          List.map
            (tsubst_data_type_def_branch (TyPoint point) index)
            branches
        ) branches points in
        replace_type type_env point (fun binder ->
          { binder with definition = Some (flag, branches) }
        )
  ) type_env
;;

(* ---------------------------------------------------------------------------- *)

(* Desugaring and checking expressions. *)

let ploc (f: env -> pattern -> env * E.pattern): env -> pattern -> env * E.pattern =
  fun (env: env) (pattern: pattern) ->
    match pattern with
    | PLocated (pattern, p1, p2) ->
        let env = locate env p1 p2 in
        let env, pattern = f env pattern in
        env, E.PLocated (pattern, p1, p2)
    | _ ->
        f env pattern
;;


let eloc (f: env -> expression -> E.expression): env -> expression -> E.expression =
  fun (env: env) (expression: expression) ->
    match expression with
    | ELocated (expression, p1, p2) ->
        let env = locate env p1 p2 in
        let expression = f env expression in
        E.ELocated (expression, p1, p2)
    | _ ->
        f env expression
;;


let dloc (f: env -> declaration -> env * E.declaration): env -> declaration -> env * E.declaration =
  fun (env: env) (declaration: declaration) ->
    match declaration with
    | DLocated (declaration, p1, p2) ->
        let env = locate env p1 p2 in
        let env, declaration = f env declaration in
        env, E.DLocated (declaration, p1, p2)
    | _ ->
        f env declaration
;;

(* [collect_and_check_pattern env pattern] performs two tasks at once: first, it
 * collects in a depth-first search all bindings in the pattern, adds them to
 * the environment, and returns the environment; second, it translates [pattern]
 * from [SurfaceSyntax.pattern] to [Expressions.pattern]. *)
let collect_and_check_pattern (env: env) (pattern: pattern): env * E.pattern =
  let env0 = env in
  let rec collect_and_check_pattern (env: env) (pattern: pattern): env * E.pattern =
    match pattern with
    | PConstraint (p, t) ->
        let env, p = collect_and_check_pattern env p in
        let t = check false env0 t KType in
        env, E.PConstraint (p, t)
    | PVar name ->
        let env = bind env (name, KTerm) in
        env, E.PVar name
    | PTuple patterns ->
        let env, patterns = List.fold_left (fun (env, patterns) pattern ->
          let env, pattern = collect_and_check_pattern env pattern in
          env, pattern :: patterns) (env, []) patterns
        in
        env, E.PTuple (List.rev patterns)
    | PConstruct (datacon, fields) ->
        let env, fieldpats = List.fold_left (fun (env, fieldpats) field ->
          let field_name, pattern = field in
          let env, pattern = collect_and_check_pattern env pattern in
          env, (field_name, pattern) :: fieldpats) (env, []) fields
        in
        env, E.PConstruct (datacon, fieldpats)
    | PLocated _ ->
        ploc collect_and_check_pattern env pattern
  in
  collect_and_check_pattern env pattern
;;

let collect_and_check_function_parameter (env: env) (t: typ): env * (Variable.name * kind) list * T.typ =
  (* Collect all the names that appear in the type. *)
  let env, bindings = extend env (bi t) in
  (* Translate the type. *)
  let t = check true env t KType in
  (* Return the enhanced environment, the bindings that were created when
   * desugaring, and the desugared type. *)
  env, bindings, t
;;


let rec collect_and_check_patexprs
    (env: env)
    (rec_flag: rec_flag)
    (patexprs: (pattern * expression) list): env * (E.pattern * E.expression) list
  = 

  let patterns, expressions = List.split patexprs in
  let sub_env, patterns = List.fold_left (fun (env, patterns) pattern ->
    let env, pattern = collect_and_check_pattern env pattern in
    env, pattern :: patterns) (env, []) patterns
  in
  let patterns = List.rev patterns in
  let check = match rec_flag with
    | Recursive -> check_expression sub_env
    | Nonrecursive -> check_expression env
  in
  let expressions = List.map check expressions in
  sub_env, List.combine patterns expressions


and check_expression (env: env) (expression: expression): E.expression =
  match expression with
  | EConstraint (e, t) ->
      let t = check false env t KType in
      let e = check_expression env e in
      E.EConstraint (e, t)

  | EVar x ->
      let kind, index = find x env in
      if kind <> KTerm then
        raise_error env (Mismatch (KTerm, kind));
      E.EVar index

  | ELet (rec_flag, patexprs, e) ->
      let env, patexprs = collect_and_check_patexprs env rec_flag patexprs in
      let e = check_expression env e in
      E.ELet (rec_flag, patexprs, e)

  | EFun (vars, params, return_type, body) ->
      (* TEMPORARY there's a bug here, this doesn't work properly in case the
       * function has multiple arguments. *)

      (* Add all the function's type parameters into the environment. *)
      let env = List.fold_left bind env vars in
      (* While desugaring the function types, [(x: τ)] will translate to
       * [∀(x::TERM), (=x, permission x: τ)], so we need to collect bindings for
       * each one of the function parameters. *)
      let env, bindings, params = List.fold_left (fun (env, bindings, params) param ->
        let env, binding, param = collect_and_check_function_parameter env param in
        env, List.rev binding :: bindings, param :: params) (env, [], []) params
      in
      let params = List.rev params in
      (* We're going great lengths to ensure we handle currified functions, even
       * though no one's every going to use them... is that really reasonable? *)
      let vars = List.flatten (vars :: bindings) in
      let return_type = check false env return_type KType in
      let body = check_expression env body in
      let r = E.EFun (vars, params, return_type, body) in
      r

  | EAssign (e1, var, e2) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      E.EAssign (e1, var, e2)

  | EAccess (e, var) ->
      let e = check_expression env e in
      E.EAccess (e, var)

  | EApply (f, arg) ->
      let f = check_expression env f in
      let arg = check_expression env arg in
      E.EApply (f, arg)

  | EMatch (e, patexprs) ->
      let e = check_expression env e in
      let patexprs = List.map (fun (pat, expr) ->
        let env, pat = collect_and_check_pattern env pat in
        let expr = check_expression env expr in
        (pat, expr)) patexprs
      in
      E.EMatch (e, patexprs)

  | ETuple exprs ->
      let exprs = List.map (check_expression env) exprs in
      E.ETuple exprs

  | EConstruct (datacon, fields) ->
      let fields = List.map (fun (name, expr) ->
        let expr = check_expression env expr in
        name, expr) fields
      in
      E.EConstruct (datacon, fields)

  | EIfThenElse (e1, e2, e3) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      let e3 = check_expression env e3 in
      E.EIfThenElse (e1, e2, e3)

  | ESequence (e1, e2) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      E.ELet (Nonrecursive, [E.PTuple [], e1], e2)

  | ELocated _ ->
      eloc check_expression env expression

  | EPlus (e1, e2) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      E.EPlus (e1, e2)

  | EMinus (e1, e2) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      E.EMinus (e1, e2)

  | ETimes (e1, e2) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      E.ETimes (e1, e2)

  | EDiv (e1, e2) ->
      let e1 = check_expression env e1 in
      let e2 = check_expression env e2 in
      E.EDiv (e1, e2)

  | EUMinus e ->
      let e = check_expression env e in
      E.EUMinus e

  | EInt i ->
      E.EInt i


and collect_and_check_declaration (env: env) (declaration: declaration): env * E.declaration =
  match declaration with
  | DMultiple (rec_flag, patexprs) ->
      let env, patexprs = collect_and_check_patexprs env rec_flag patexprs in
      env, E.DMultiple (rec_flag, patexprs)
  | DLocated _ ->
     dloc collect_and_check_declaration env declaration
;;


(* This function transforms a [SurfaceSyntax.expression] into an
 * [Expressions.expression] while converting everything into a De Bruijn
 * representation (indices) and checking that the types that appear in the
 * expression are correct. *)
let check_declaration_group (env: env) (declarations: declaration_group): Expressions.declaration_group =
  let _env, declarations = List.fold_left (fun (env, declarations) declaration ->
    let env, declaration = collect_and_check_declaration env declaration in
    env, declaration :: declarations) (env, []) declarations
  in
  List.rev declarations
;;

let check_program (type_env: T.env) (program: program): T.env * Expressions.declaration_group
  =
  let data_type_group, declaration_group = program in
  (* [env] is a [WellKindedness.env]; we need it to translate the declarations
   *   because the data type declarations are bound in it already, and we freely
   *   mix type binders and expr binders.
   * [points] is a [(level, point) list]: we need it to replace all [TyVar]s
   *   that refer to data types in the declarations by the corresponding points.
   * [type_env] is a [Types.env]; we need it for the rest of the type-checker.
   * *)
  let env, points, type_env = check_data_type_group type_env empty data_type_group in
  (* This desugars everything, including function types present in the various
   * declarations, and also translates this into a [Types.declaration list]. *)
  let declarations = check_declaration_group env declaration_group in
  (* However, at this stage, there's only [TyVar]s in the declarations. We need
   * to replace those that refer to data types with the corresponding
   * [TyPoint]s. *)
  let total_number_of_data_types = List.length points in
  let subst_decl = fun declarations ->
    List.fold_left (fun declarations (level, point) ->
      let index = total_number_of_data_types - level - 1 in
      E.tsubst_decl (T.TyPoint point) index declarations
    ) declarations points
  in
  let declarations = subst_decl declarations in
  type_env, declarations
;;


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
    let defs = map_types env (fun { names; kind } { definition; _ } ->
      let name = List.hd names in
      match definition with
      | Some (flag, branches) ->
          print_data_type_def env flag name kind branches
      | None ->
          print_abstract_type_def env name kind
    ) in
    join (break1 ^^ break1) defs
  ;;

  let print_kinds_and_facts program_env =
    string "KINDS:" ^^ nest 2 (hardline ^^ print_kinds program_env) ^^ hardline ^^
    hardline ^^
    string "FACTS:" ^^ nest 2 (hardline ^^ print_facts program_env) ^^ hardline
  ;;

end

