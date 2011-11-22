(* This module implements a well-kindedness check for the types of
   the surface language. *)

open SurfaceSyntax

(* ---------------------------------------------------------------------------- *)

(* Environments map identifiers to kinds. *)

module M =
  Patricia.Little

type env =
    kind M.t

(* Sets of identifiers. *)

module S =
  M.Domain

(* ---------------------------------------------------------------------------- *)

let unbound x =
  assert false (* TEMPORARY *)

let mismatch expected_kind inferred_kind =
  assert false (* TEMPORARY *)

let arrow_expected kind =
  assert false (* TEMPORARY *)

let illegal_consumes () =
  assert false (* TEMPORARY *)

let illegal_named_tuple_component x =
  assert false (* TEMPORARY *)

let deconstruct_arrow = function
  | KArrow (ty1, ty2) ->
      ty1, ty2
  | kind ->
      arrow_expected kind

let strict_add x identifiers =
  assert false (* TEMPORARY *) (* possibly use extended version of [gSet] *)

let rec bi = function
  | TyTuple [ (ConsumesAndProduces, TyTupleComponentAnonymousValue ty) ] ->
      (* A tuple of one anonymous component is interpreted as a pair
	 of parentheses. *)
      bi ty
  | TyTuple components ->
      (* A tuple type can bind names for some or all of its components. *)
      List.fold_left (fun identifiers (_, component) ->
	match component with
	| TyTupleComponentNamedValue (x, _) ->
	    (* These names must be distinct. *)
	    strict_add x identifiers
	| TyTupleComponentAnonymousValue _
	| TyTupleComponentPermission _ ->
	    identifiers
      ) S.empty components
  | _ ->
      (* A non-tuple type does not bind any names. *)
      S.empty

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
      (* Gather the names bound by the left-hand side, if any. *)
      let identifiers = bi ty1 in
      (* These names are bound in the left-hand and right-hand sides.
	 Yes, this means that recursive dependencies are permitted. *)
      let env = S.fold (fun x env ->
	M.add x KType env
      ) identifiers env in
      (* Check the left-hand and right-hand sides. *)
      check true env ty1 KType;
      check false env ty2 KType;
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

