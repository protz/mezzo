open SurfaceSyntax
open InterpreterDefs

(* This is the Mezzo interpreter. *)

(* ---------------------------------------------------------------------------- *)

(* An empty interpreter environment. *)

let empty_env : env = {
  variables = V.empty;
  datacons = D.empty;
}

(* Extending the environment with a new unqualified variable. *)

let extend_unqualified_variable x v env =
  { env with variables = V.extend_unqualified x v env.variables }

(* Opening a module. *)

let unqualify m env =
  {
    variables = V.unqualify m env.variables;
    datacons = D.unqualify m env.datacons;
  }

(* ---------------------------------------------------------------------------- *)

(* Constant value definitions. *)

(* The unit value is the empty tuple. *)

let unit_value =
  VTuple []

(* The Boolean values are [core::True] and [core::False]. *)

let false_value =
  VAddress { tag = 0; adopter = None; fields = [||] }

let true_value =
  VAddress { tag = 1; adopter = None; fields = [||] }

(* ---------------------------------------------------------------------------- *)

(* Un-tagging values. *)

let asBlock (v : value) : block =
  match v with
  | VAddress block ->
      block
  | _ ->
      (* Runtime tag error. *)
      assert false

let asTuple (v : value) : value list =
  match v with
  | VTuple vs ->
      vs
  | _ ->
      (* Runtime tag error. *)
      assert false

let asClosure (v : value) : closure =
  match v with
  | VClosure c ->
      c
  | _ ->
      (* Runtime tag error. *)
      assert false

(* ---------------------------------------------------------------------------- *)

(* Exploiting information about data constructors. *)

(* Finding a field in a table. *)

let find_field (f : Variable.name) (fields : 'a Variable.Map.t) : 'a =
  try
    Variable.Map.find f fields
  with Not_found ->
    (* Unknown field. *)
    assert false

(* Translating a data-constructor-and-field pair to an integer offset. *)

let field_offset (env : env) (field : field) : int =
  (* Look up this data constructor. *)
  let info = D.lookup_unqualified field.field_datacon env.datacons in
  (* Find this field's offset. *)
  find_field field.field_name info.datacon_fields

(* Translating a data constructor to an index. *)

let datacon_index (env : env) (datacon : Datacon.name) : int =
  let info = D.lookup_unqualified datacon env.datacons in
  info.datacon_index

(* ---------------------------------------------------------------------------- *)

(* Translating a type to a pattern. *)

let rec type_to_pattern (ty : typ) : pattern =
  match ty with

  (* A structural type constructor is translated to the corresponding
     structural pattern. *)

  | TyTuple tys ->
      PTuple (List.map type_to_pattern tys)

  | TyConcreteUnfolded (datacon, fields) ->
      let fps =
	List.fold_left (fun fps field ->
	  match field with
          | FieldValue (f, ty) -> (f, type_to_pattern ty) :: fps
          | FieldPermission _  -> fps
	) [] fields in
      PConstruct (datacon, fps)

   (* A name introduction gives rise to a variable pattern. *)

  | TyNameIntro (x, ty) ->
      PAs (type_to_pattern ty, PVar x)

  (* Pass (go down into) the following constructs. *)

  | TyLocated (ty, _, _)
  | TyAnd (_, ty)
  | TyConsumes ty
  | TyBar (ty, _) ->
      type_to_pattern ty

  (* Stop at (do not go down into) the following constructs. *)

  | TyForall _
  | TyUnknown
  | TyArrow _ 
  | TySingleton _
  | TyQualified _
  | TyDynamic
  | TyApp _
  | TyVar _ ->
      PAny

  (* The following cases should not arise. *)

  | TyEmpty
  | TyStar _
  | TyAnchoredPermission _ ->
      (* Type of kind PERM, where a type of kind TERM was expected. *)
      assert false

(* ---------------------------------------------------------------------------- *)

(* Matching a value [v] against a pattern [p]. The resulting bindings are
   accumulated in the environment [env]. *)

(* The data constructors that appear in the pattern [p] are interpreted
   using the same environment [env] that serves as an accumulator. This
   may seem slightly dirty, but is ok: [env] serves an accumulator for
   variable bindings, so as far as data constructor bindings are concerned,
   it remains unchanged as we progress through the matching process. *)

(* The main function, [match_pattern], raises [MatchFailure] if [p] does not
   match [v]. The following two functions, [match_irrefutable_pattern] and
   [match_refutable_pattern], catch this exception. *)

exception MatchFailure

let rec match_pattern (env : env) (p : pattern) (v : value) : env =
  match p with
  | PVar x ->
      extend_unqualified_variable x v env
  | PTuple ps ->
      begin try
	List.fold_left2 match_pattern env ps (asTuple v)
      with Invalid_argument _ ->
	(* Tuples of non-matching lengths. *)
	assert false
      end
  | PConstruct (datacon, fps) ->
      let b = asBlock v in
      let info = D.lookup_unqualified datacon env.datacons in
      if info.datacon_index = b.tag then
	let fields = b.fields in
        List.fold_left (fun env (f, p) ->
	  let offset = find_field f info.datacon_fields in
	  match_pattern env p fields.(offset)
	) env fps
      else
        raise MatchFailure
  | PLocated (p, _, _)
  | PConstraint (p, _) ->
      match_pattern env p v
  | PAs (p1, p2) ->
      let env = match_pattern env p1 v in
      let env = match_pattern env p2 v in
      env
  | PAny ->
      env

let match_irrefutable_pattern (env : env) (p : pattern) (v : value) : env =
  try
    match_pattern env p v
  with MatchFailure ->
    (* This pattern was supposed to be irrefutable! *)
    assert false

let match_refutable_pattern (env : env) (p : pattern) (v : value) : env option =
  try
    Some (match_pattern env p v)
  with MatchFailure ->
    None

(* ---------------------------------------------------------------------------- *)

(* Evaluating an expression. *)

let rec eval (env : env) (e : expression) : value =
  match e with

  | EConstraint (e, _) ->
      eval env e

  | EVar x ->
      V.lookup_unqualified x env.variables

  | EQualified (m, x) ->
      V.lookup_qualified m x env.variables

  | ELet (Nonrecursive, equations, body) ->
      (* Evaluate the equations, in left-to-right order. *)
      let new_env : env =
	List.fold_left (fun new_env (p, e) ->
	  (* For each equation [p = e], evaluate the expression [e] in the old
	     environment [env], and match the resulting value against the
	     pattern [p]. Accumulate the resulting bindings in the new
	     environment [new_env]. The type-checker guarantees that no
	     variable is bound twice. *)
	  match_irrefutable_pattern new_env p (eval env e)
	) env equations
      in
      (* Evaluate the body. *)
      eval new_env body

  | ELet (Recursive, equations, body) ->
      (* We must construct an environment and a number of closures
	 that point to each other; this is Landin's knot. We begin
         by constructing a list of partly initialized closures, as
         well as the new environment, which contains these closures. *)
      let (new_env : env), (closures : closure list) =
	List.fold_left (fun (new_env, closures) (p, e) ->
	  match p, e with
	  | PVar f, EFun (_type_parameters, argument_type, _result_type, body) ->
	      (* Build a closure with an uninitialized environment field. *)
	      let c = {
		(* The argument pattern is implicit in the argument type. *)
		arg = type_to_pattern argument_type;
		(* The function body. *)
		body = body;
		(* An uninitialized environment. *)
		env = empty_env;
	      } in
	      (* Bind [f] to this closure. *)
	      extend_unqualified_variable f (VClosure c) new_env,
	      c :: closures
	  | _, _ ->
	      (* The left-hand side of a recursive definition must be a variable,
		 and the right-hand side must be a lambda-abstraction. *)
	      (* TEMPORARY should deal with PLocated too *)
	      assert false
	) (env, []) equations
      in
      (* There remains to patch the closures with the new environment. *)
      List.iter (fun c ->
	(* TEMPORARY environment could/should be filtered *)
        c.env <- new_env
      ) closures;
      (* Evaluate the body. *)
      eval new_env body

  | EFun (_type_parameters, argument_type, _result_type, body) ->
      VClosure {
	(* The argument pattern is implicit in the argument type. *)
	arg = type_to_pattern argument_type;
	(* The function body. *)
	body = body;
	(* The environment. *)
	(* TEMPORARY environment could/should be filtered *)
	env = env;
      }

  | EAssign (e1, field, e2) ->
      let b1 = asBlock (eval env e1) in
      let v2 = eval env e2 in
      b1.fields.(field_offset env field) <- v2;
      unit_value

  | EAssignTag (e, { new_datacon; previous_datacon }) ->
      let b = asBlock (eval env e) in
      assert (b.tag = datacon_index env previous_datacon);
      b.tag <- datacon_index env new_datacon;
      unit_value

  | EAccess (e, field) ->
      let b = asBlock (eval env e) in
      b.fields.(field_offset env field)

  | EAssert _ ->
      unit_value

  | EApply (e1, e2) ->
      let c1 = asClosure (eval env e1) in
      let v2 = eval env e2 in
      (* Extend the closure's environment with a binding of the
	 formal argument to the actual argument. Evaluate the
	 closure body. *)
      eval (match_irrefutable_pattern c1.env c1.arg v2) c1.body

  | ETApply (e, _) ->
      eval env e

  | EMatch (_, e, branches) ->
      switch env (eval env e) branches

  | ETuple es ->
      (* [List.map] implements left-to-right evaluation. *)
      VTuple (List.map (eval env) es)

  | EConstruct (datacon, fes) ->
      (* Evaluate the fields in the order specified by the programmer. *)
      let fvs =
	List.map (fun (f, e) -> (f, eval env e)) fes
      in
      (* Allocate a field array. *)
      let info = D.lookup_unqualified datacon env.datacons in
      let fields = Array.create info.datacon_arity unit_value in
      (* Populate the field array. *)
      List.iter (fun (f, v) ->
	let offset = find_field f info.datacon_fields in
	fields.(offset) <- v
      ) fvs;
      (* Allocate a memory block. *)
      VAddress {
	tag = info.datacon_index;
	adopter = None;
	fields = fields;
      }

  | EIfThenElse (_, e, e1, e2) ->
      let b = asBlock (eval env e) in
      eval env (if b.tag > 0 then e1 else e2)

  | ESequence (e1, e2) ->
      let _unit = eval env e1 in
      eval env e2

  | ELocated (e, pos1, pos2) ->
      (* TEMPORARY keep track of locations for runtime error messages *)
      eval env e

  | EInt i ->
      VInt i

  | EExplained e ->
      eval env e

  | EGive (e1, e2) ->
      let b1 = asBlock (eval env e1) in
      let b2 = asBlock (eval env e2) in
      assert (b1.adopter = None);
      b1.adopter <- Some b2;
      unit_value

  | ETake (e1, e2) ->
      let b1 = asBlock (eval env e1) in
      let b2 = asBlock (eval env e2) in
      begin match b1.adopter with
      | Some b when (b == b2) ->
          b1.adopter <- None;
          unit_value
      | _ ->
          Log.error "Take failure.\n"
      end

  | EOwns (e1, e2) ->
      let b1 = asBlock (eval env e1) in
      let b2 = asBlock (eval env e2) in
      begin match b1.adopter with
      | Some b when (b == b2) ->
	  true_value
      | _ ->
          false_value
      end

  | EFail ->
      Log.error "Failure.\n"

(* ---------------------------------------------------------------------------- *)

(* Evaluating a switch construct. *)

and switch (env : env) (v : value) (branches : (pattern * expression) list) : value =
  match branches with
  | (p, e) :: branches ->
      begin match match_refutable_pattern env p v with
      | Some env ->
	  (* [p] matches [v]. Evaluate the branch [e]. *)
	  eval env e
      | None ->
	  (* [p] does not match [v]. Try the next branch. *)
	  switch env v branches
      end
  | [] ->
      (* No more branches. This should not happen if the type-checker has
         checked for exhaustiveness. At the moment, this is not done,
         though. *)
      (* TEMPORARY should print a location and the value [v] *)
      Log.error "Match failure.\n"

(* ---------------------------------------------------------------------------- *)

(* Evaluating a value definition. *)

let eval_value_definition (env : env) (def : declaration) : env =
  failwith "UNIMPLEMENTED"

(* Evaluating a concrete data type definition. *)

let evaluate_data_type_def (env : env) (rhs : data_type_def_rhs) : env =
  failwith "UNIMPLEMENTED"

(* ---------------------------------------------------------------------------- *)

(* Evaluating a toplevel item. *)

let eval_item (env: env) (item: toplevel_item) : env =
  match item with
  | ValueDeclarations defs ->
      List.fold_left eval_value_definition env defs
  | OpenDirective m ->
      (* Assuming that the module [m] has been evaluated before, the (public)
	 qualified names that it has declared are available in the environment.
	 For each name of the form [m::x], we create a new local name [x]. *)
      unqualify m env
  | DataTypeGroup (_, defs) ->
      List.fold_left (fun env def ->
        match def with
        | Concrete (_, _, rhs, _) ->
            evaluate_data_type_def env rhs
        | Abstract _ ->
            env
      ) env defs
  | PermDeclaration _ ->
      (* We evaluate only implementations, not interfaces. *)
      assert false
