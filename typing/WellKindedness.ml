(* This module implements a well-kindedness check for the types of
   the surface language. *)

open SurfaceSyntax

(* ---------------------------------------------------------------------------- *)

(* Kind constructors. *)

let karrow bindings kind =
  List.fold_right (fun (x, kind1) kind2 ->
    KArrow (kind1, kind2)
  ) bindings kind

(* ---------------------------------------------------------------------------- *)

(* Environments map identifiers to kinds. *)

module M =
  Patricia.Little

type env =
    kind M.t

let empty =
    M.empty

(* ---------------------------------------------------------------------------- *)

(* Error messages. *)

let unbound x =
  assert false (* TEMPORARY *)

let mismatch expected_kind inferred_kind =
  assert false (* TEMPORARY *)

let illegal_consumes () =
  assert false (* TEMPORARY *)

let illegal_named_tuple_component x =
  assert false (* TEMPORARY *)

let deconstruct_arrow = function
  | KArrow (ty1, ty2) ->
      ty1, ty2
  | kind ->
      assert false (* TEMPORARY *)

let strict_add x kind env =
  try
    M.strict_add x kind env
  with M.Unchanged ->
    assert false (* TEMPORARY *)

(* ---------------------------------------------------------------------------- *)

(* [bi ty] produces a set of the identifiers that are brought into scope by
   the type [ty], when this type is found on the left-hand side of an arrow.
   In short, a tuple type can bind names for some or all of its components;
   any other type does not bind any names. *)

let rec bi ty : env =
  match ty with
  | TyTuple [ (ConsumesAndProduces, TyTupleComponentAnonymousValue ty) ] ->
      (* A tuple of one anonymous component is interpreted as a pair
	 of parentheses. *)
      bi ty
  | TyTuple components ->
      (* A tuple type can bind names for some or all of its components. *)
      List.fold_left (fun env (_, component) ->
	match component with
	| TyTupleComponentNamedValue (x, _) ->
	    (* These names must be distinct. *)
	    strict_add x KType env
	| TyTupleComponentAnonymousValue _
	| TyTupleComponentPermission _ ->
	    env
      ) M.empty components
  | _ ->
      (* A non-tuple type does not bind any names. *)
      M.empty

(* ---------------------------------------------------------------------------- *)

(* [infer special env ty] and [check special env ty kind] perform bottom-up
   kind inference and kind checking. The flag [special] tells whether we are
   under the left-hand side of an arrow. The environment [env] maps variables
   to kinds. *)

let rec infer special env = function
  | TyTuple [ (ConsumesAndProduces, TyTupleComponentAnonymousValue ty) ] ->
      (* A tuple of one anonymous component is interpreted as a pair
	 of parentheses. This special case is important: without it,
         any type that is placed within parentheses would be viewed
	 as a tuple, hence it would be forced to have kind [KType]. *)
      infer special env ty
  | TyTuple components ->
      List.iter (check_tuple_type_component special env) components;
      KType
  | TyUnknown ->
      KType
  | TyDynamic ->
      KType
  | TyEmpty ->
      KPerm
  | TyVar x ->
      begin try
	M.find x env
      with Not_found ->
	unbound x
      end
  | TyConcreteUnfolded (datacon, fields) ->
      (* TEMPORARY check that this is consistent with the definition of datacon *)
      List.iter (check_data_field_def env) fields;
      KType
  | TySingleton x ->
      check false env (TyVar x) KTerm;
      KType
  | TyApp (ty1, ty2) ->
      let domain, codomain = deconstruct_arrow (infer false env ty1) in
      check false env ty2 domain;
      codomain
  | TyArrow (ty1, ty2) ->
      (* Gather the names bound by the left-hand side, if any. These names
	 are bound in the left-hand and right-hand sides. Yes, this means
	 that recursive dependencies are permitted. *)
      let env = M.union env (bi ty1) in
      (* Check the left-hand and right-hand sides. *)
      check true env ty1 KType;
      check false env ty2 KType;
      KType
  | TyForall ((x, kind), ty) ->
      let env = M.add x kind env in
      (* It seems that we can require the body of a universal type to
	 have type [KType]. Allowing [KTerm] does not make sense, and
	 allowing [KPerm] makes sense but does not sound useful in
	 practice. *)
      check false env ty KType;
      KType
  | TyAnchoredPermission (x, ty) ->
      check false env (TyVar x) KTerm;
      check false env ty KType;
      KPerm
  | TyStar (ty1, ty2) ->
      check false env ty1 KPerm;
      check false env ty2 KPerm;
      KPerm

and check special env ty expected_kind : unit =
  let inferred_kind = infer special env ty in
  if expected_kind <> inferred_kind (* generic equality at kinds! *)
  then mismatch expected_kind inferred_kind

and check_tuple_type_component special env (annotation, component) =
  (* Check that [consumes] is used only where meaningful, that is,
     only under the left-hand side of an arrow. Similarly, named
     tuple components are permitted only under the left-hand side
     of an arrow. *)
  begin match annotation, component, special with
  | Consumes, _, false ->
      illegal_consumes ()
  | _, TyTupleComponentNamedValue (x, _), false ->
      illegal_named_tuple_component x
  | _, _, _ ->
      ()
  end;
  (* Check this tuple component. *)
  match component with
  | TyTupleComponentAnonymousValue ty
  | TyTupleComponentNamedValue (_, ty) ->
      check false env ty KType
  | TyTupleComponentPermission ty ->
      check false env ty KPerm

and check_data_field_def env = function
  | FieldValue (_, ty) ->
      check false env ty KType
  | FieldPermission ty ->
      check false env ty KPerm

(* ---------------------------------------------------------------------------- *)

(* Kind checking for algebraic data type definitions. *)

let check_data_type_def_branch env (datacon, fields) =
  List.iter (check_data_field_def env) fields

let check_data_type_def_rhs env rhs =
  List.iter (check_data_type_def_branch env) rhs

let collect_data_type_def_lhs_parameters env (tycon, bindings) : env =
  (* Do not bother checking that the parameters are distinct. *)
  List.fold_left (fun env (x, kind) ->
    M.add x kind env
  ) env bindings

let check_data_type_def env (lhs, rhs) =
  check_data_type_def_rhs (collect_data_type_def_lhs_parameters env lhs) rhs

let collect_data_type_def_lhs_tycon env (tycon, bindings) : env =
  strict_add tycon (karrow bindings KType) env

let collect_data_type_def_tycon env (lhs, _) : env =
  collect_data_type_def_lhs_tycon env lhs

let collect_data_type_group_tycon group : env =
  List.fold_left collect_data_type_def_tycon M.empty group

let check_data_type_group env group : env =
  (* Collect the names and kinds of the data types that are being
     defined. Check that they are distinct. Extend the environment. *)
  let env = M.union env (collect_data_type_group_tycon group) in
  (* Check every data type definition. *)
  List.iter (check_data_type_def env) group;
  (* Return the extended environment. *)
  env

