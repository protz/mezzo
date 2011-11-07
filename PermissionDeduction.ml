open Data
module U = PersistentUnionFind
module IntMap = Patricia.Little

(* ---------------------------------------------------------------------------- *)

(* A typing context is either inconsistent (which means that it represents a
   set of incompatible assumptions) or consistent. *)

type context =
  | Inconsistent
  | Consistent of consistent_context

(* ---------------------------------------------------------------------------- *)

(* A consistent typing context is a tuple of the following information. *)

and consistent_context = {

  (* How many type variables are in scope. *)
  type_depth: int;
 
  (* How many term variables are in scope. *)
  term_depth: int;

  (* A mapping of the term variables in scope to points of the union-find
     algorithm. *)
  points: U.point IntMap.t;

  (* A state of the union-find algorithm maintains aliasing information
     (that is, equalities between points) as well as a mapping of points
     to canonical permissions. *)
  state: ustate;

}

and ustate =
    canonical_permission U.state

(* ---------------------------------------------------------------------------- *)

(* A canonical permission is a conjunction of permissions in the usual
   sense. These permissions are (folded or unfolded) concrete types and
   abstract types. (There are no [TySingleton] permissions, because equalities
   between objects are encoded in the state of the union-find algorithm; there
   are no [TyNone] permissions, because they are trivial.) Furthermore, the
   concrete permissions are as follows: either there is exactly one unfolded
   concrete permission, and each field holds a [TySingleton] permission; or
   there is a list of folded concrete permissions and they are unfoldable
   (because the algebraic data type has more than one branch). In the latter
   case, all folded concrete permissions must be for the same [tycon],
   possibly with distinct parameters. *)

and canonical_permission = {
  concrete_permissions: concrete_permissions;
  abstract_permissions: abstract_type list
}

and concrete_permissions =
  | Unfolded of datacon * (field * U.point) list
  | Folded of (* unfoldable *) concrete_type list

(* ---------------------------------------------------------------------------- *)

(* The user may test whether a typing context is consistent. *)

let is_inconsistent = function
  | Inconsistent ->
      true
  | Consistent _ ->
      false

(* ---------------------------------------------------------------------------- *)

(* TEMPORARY move to module [Data] *)

let is_exclusive_datacon datacon : bool =
  assert false

let eq_tycon tycon1 tycon2 : bool =
  assert false

let eq_datacon datacon1 datacon2 : bool =
  assert false

let eq_field field1 field2 : bool =
  assert false

(* ---------------------------------------------------------------------------- *)

(* Iteration over two lists of fields for the same [datacon]. We
   assume that the order of fields is fixed and corresponds to
   the order found in class definition. *)

let rec iter2_fields f fields1 fields2 =
  match fields1, fields2 with
  | [], [] ->
      ()
  | (field1, data1) :: fields1, (field2, data2) :: fields2 ->
      assert (eq_field field1 field2);
      f data1 data2;
      iter2_fields f fields1 fields2
  | _ :: _, []
  | [], _ :: _ ->
      assert false

(* ---------------------------------------------------------------------------- *)

(* [lookup_termvar context x] is the union-find point associated with the term
   variable [x]. *)

let lookup_termvar context (x : termvar) : U.point =
  assert (x < context.term_depth);
  try
    IntMap.find x context.points
  with Not_found ->
    assert false

(* ---------------------------------------------------------------------------- *)

(* There are two important ways of updating a context (to produce a
   new context). One is the addition of an equality, that is, the
   unification of two points [x1] and [x2]. The other is the addition
   of a permission [x: ty], where [x] is a point and [ty] is a type. *)

(* The code that performs these operations is written in an imperative style:
   there is a current context and a queue of pending operations. This style is
   slightly more convenient than a side-effect-free and recursive style. It
   could also be easier to debug, as the contents of the queue can be
   printed. *)

(* A functor is used in order to allow the mutable state to be created
   and shared by the various functions. *)

(* TEMPORARY BUG [type_depth] is never used: must lift types found in
   algebraic data type definitions into the local context *)

module ContextUpdate (X : sig

  (* The initial context. *)
  val context: consistent_context

end) = struct

  (* The current context. *)

  let current_context =
    ref X.context

  (* The queue of currently pending operations. *)

  type operation =
    | OpUnify of U.point * U.point
    | OpAdd of U.point * typ

  let pending_operations : operation Queue.t =
    Queue.create()

  (* This exception is raised if the current context is found to be
     inconsistent. *)

  exception Inconsistency

  (* [request_unify x1 x2] enqueues a unification request. *)

  let request_unify x1 x2 : unit =
    Queue.add (OpUnify (x1, x2)) pending_operations

  (* [request_add x ty] enqueues a permission addition request. *)

  let request_add x ty : unit =
    Queue.add (OpAdd (x, ty)) pending_operations

  (* These auxiliary functions update the current context by applying
     the operation [op] to the state of the union-find algorithm. *)

  let ufop (op : ustate -> ustate) : unit =
    let context = !current_context in
    current_context := { context with state = op context.state }

  let ufopr (op : ustate -> 'result * ustate) : 'result =
    let context = !current_context in
    let result, state = op context.state in
    current_context := { context with state = state };
    result

  (* [merge_concrete cperm1 cperm2] merges the concrete permissions
     [cperm1] and [cperm2], producing a new canonical permission.
     It may schedule new operations and/or raise [Inconsistency]. *)

  let merge_concrete cperm1 cperm2 : concrete_permissions =
    match cperm1, cperm2 with

    | Unfolded (datacon1, fields1), Unfolded (datacon2, fields2) ->
	(* We have two unfolded permissions. *)
	(* An object cannot simultaneously carry two distinct tags, so
	   [datacon1] and [datacon2] must coincide, or this typing context
	   is inconsistent. *)
	if not (eq_datacon datacon1 datacon2) then
	  raise Inconsistency;
	(* The class with which [datacon1] is associated cannot be exclusive,
	   or this typing context is inconsistent. *)
	if is_exclusive_datacon datacon1 then
	  raise Inconsistency;
	(* Thus, both permissions are duplicable. In fact, this must be two
	   copies of the same permission: we can unify the fields. Schedule
	   unification requests. *)
	iter2_fields request_unify fields1 fields2;
	(* The two permissions are now equivalent. Keep either of them. *)
	cperm1

    | (Unfolded (datacon, fields1) as cperm1), Folded ctys
    | Folded ctys, (Unfolded (datacon, fields1) as cperm1) ->
	(* We have one unfolded permission. This permission tells us
	   which branch we are in, and gives us sufficient information
	   to unfold any as-yet-unfolded permissions found on the other
	   side. *)
	List.iter (fun cty ->
	  if is_exclusive_datacon datacon then
	    raise Inconsistency;
	  (* Out of the definition of [tycon], extract the definition
	     of [datacon], and instantiate it appropriately. Here, we
	     prepare the instantiation function, and use it on the fly
	     below. *)
	  let instantiate, definition = unfold_concrete_type cty in
	  match find_branch definition datacon with
	  | None ->
	      raise Inconsistency
	  | Some { fields = fields2 } ->
	      iter2_fields (fun x1 ty2 ->
		(* For each field, in [fields1], we find a name [x1],
		   and in [fields2], we find a type [ty2]. We must
		   then add the permission [x1: ty2] to the context.
		   Schedule a request. *)
		request_add x1 (instantiate ty2)
	      ) fields1 fields2
	) ctys;
        (* Keep the unfolded permission. *)
        cperm1

    | Folded ctys1, Folded ctys2 ->
	(* We have folded permissions only. Basically, all we have to
	   do is concatenate the two lists of permissions. There is
	   only one thing to check: all permissions must be for the
	   same [tycon], because it is impossible for an object to
	   inhabit two distinct algebraic data type *constructors*.
	   For instance, an object cannot be both a pair and a list.
	   It can be both a pair of this and a pair of that, though,
	   so it *can* inhabit two distinct concrete *types*. *)
	match ctys1, ctys2 with
	| [], ctys
	| ctys, [] ->
	    Folded ctys
	| (tycon1, _, _) :: _, (tycon2, _, _) :: _ ->
	    if not (eq_tycon tycon1 tycon2) then
	      raise Inconsistency;
	    Folded (ctys1 @ ctys2)

  (* [merge perm1 perm2] merges the canonical permissions [perm1] and [perm2],
     producing a new canonical permission. It may schedule new operations
     and/or raise [Inconsistency]. *)

  let merge perm1 perm2 : canonical_permission =

    (* Concrete and abstract permissions are merged independently: there is no
       interaction between a concrete permission and an abstract one. *)

    (* Lists of abstract permissions are merged by simple concatenation. *)

    {
      concrete_permissions =
	merge_concrete perm1.concrete_permissions perm2.concrete_permissions;
      abstract_permissions =
	perm1.abstract_permissions @ perm2.abstract_permissions;
    }

  (* [unify x1 x2] adds the equation [x1 = x2] to the current context.
     It may schedule new operations and/or raise [Inconsistency]. *)

  let unify (x1 : U.point) (x2 : U.point) : unit =

    (* If the equality [x1 = x2] is already known, then there is nothing to
       do. Otherwise, add this equality to the state of the union-find
       algorithm, and merge the canonical permissions associated with [x1] and
       [x2]. *)

    ufop (U.union_computed merge x1 x2)

  (* [add x ty] adds the (non-canonical) permission [x: ty] to the current
     context. It may schedule new operations and/or raise [Inconsistency]. *)

  let rec add (x : U.point) (ty : typ) : unit =
    match ty with
    | TySingleton y ->
        (* A permission of the form [x: (=y)] is turned into an equation
	   [x = y]. *)
        request_unify x (lookup_termvar !current_context y)
    | TyTop ->
        (* A permission of the form [x: none] is discarded. *)
        ()
    | TyConcreteFolded cty ->
        (* A folded concrete permission must be unfolded if this algebraic
	   data type has at most one constructor. *)
        let instantiate, definition = unfold_concrete_type cty in
	begin match definition.branches with
	| [] ->
	    (* If we have proof that [x] inhabits an empty type, then
	       this typing context is inconsistent. *)
	    raise Inconsistency
	| [ { datacon; fields } ] ->
	    (* This permission can be unfolded. We do so eagerly.
	       There is a risk of non-termination, which we do not
	       address (for the moment). *)
	    let fields = List.map (fun (field, ty) -> (field, instantiate ty)) fields in
	    add x (TyConcreteUnfolded (datacon, fields))
	| _ :: _ :: _ ->
	    (* This permission cannot be unfolded, because there are
	       at least two branches. It is a canonical permission. *)
	    let perm = {
	      concrete_permissions = Folded [ cty ];
	      abstract_permissions = []
	    } in
	    (* Merge the canonical permission that is already associated
	       with [x] and the canonical permission computed above. *)
	    ufop (U.update (merge perm) x)
	end
    | TyConcreteUnfolded (datacon, fields) ->
        (* An unfolded concrete permission can be considered a canonical
	   permission if each field is named by a point. Introduce a fresh
	   point for each field, and schedule a permission addition for
	   each of these points. *)
        let no_permission = {
	  concrete_permissions = Folded [];
	  abstract_permissions = []
	} in
        let points : (field * U.point) list =
	  List.map (fun (field, ty) ->
	    let y = ufopr (U.create no_permission) in
	    request_add y ty;
	    field, y
          ) fields
	in
	(* Build and install a canonical permission. *)
	let perm = {
	  concrete_permissions = Unfolded (datacon, points);
	  abstract_permissions = []
	} in
	ufop (U.update (merge perm) x)
    | TyAbstract aty ->
        (* An abstract permission can be considered a canonical permission.
	   Build it and install it. *)
	let perm = {
	  concrete_permissions = Folded [];
	  abstract_permissions = [ aty ]
	} in
	ufop (U.update (merge perm) x)

  (* There remains to repeatedly process the requests. *)

  let rec run () : consistent_context =
    let finished =
      try
	begin match Queue.take pending_operations with
	| OpUnify (x1, x2) ->
	    unify x1 x2
	| OpAdd (x, ty) ->
	    add x ty
	end;
	false
      with Queue.Empty ->
	true
    in
    if finished then
      !current_context
    else
      run()

  let unify x1 x2 : consistent_context =
    unify x1 x2;
    run()

  let add x ty : consistent_context =
    add x ty;
    run()

end

(* The functions [unify] and [add] are the public entry points to the
   above code. *)

let unify (x1 : termvar) (x2 : termvar) (context : context) : context =
  match context with
  | Inconsistent ->
      Inconsistent
  | Consistent context ->
      let module CU = ContextUpdate(struct let context = context end) in
      try
        Consistent (CU.unify (lookup_termvar context x1) (lookup_termvar context x2))
      with CU.Inconsistency ->
	Inconsistent

let add (x : termvar) (ty : typ) (context : context) : context =
  match context with
  | Inconsistent ->
      Inconsistent
  | Consistent context ->
      let module CU = ContextUpdate(struct let context = context end) in
      try
        Consistent (CU.add (lookup_termvar context x) ty)
      with CU.Inconsistency ->
	Inconsistent

