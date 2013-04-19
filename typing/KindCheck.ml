(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

(* Note by Jonathan: a clean version of the kind checking rules can be
   found in my thesis noteboook, date June, 16th 2012. *)

open Kind
open SurfaceSyntax

(* ---------------------------------------------------------------------------- *)

(* A local identifier (one that is defined in the current module) is represented
   as a de Bruijn level (not to be confused with a de Bruijn index!). This is an
   implementation detail of [KindCheck] and does not affect its clients. *)

type level =
    int

(* An external identifier (one that is defined in another module) is represented
   as a value of type ['v]. Think of it as a binder that has been opened already. *)

(* Thus, for our purposes, a [var] is either a local name or a non-local name. *)

(* There is a subtlety concerning the meaning of the integer argument carried
   by [Local]. Internally, an environment contains [var]s represented using
   de Bruijn levels. However, the public functions that export variables,
   namely [find_var] and [find_datacon], produce [var]s represented using de
   Bruijn indices. *)

type 'v var =
       Local of level
  | NonLocal of 'v

(* These data structures are used to keep track of the known variables and data
   constructors. *)

module V =
  Namespace.MakeNamespace(Variable)

module D =
  Namespace.MakeNamespace(Datacon)

(* The environments defined here are used for kind checking and for translating
   types down to the core syntax. *)

type 'v env = {

  (* The current de Bruijn level. *)
  level: level;

  (* A mapping of (qualified or unqualified) variable names to pairs of a kind
     and a variable. *)
  variables: ('v var * kind) V.global_env;

  (* A mapping of (qualified or unqualified) data constructor names to a pair
     of a variable (the algebraic data type with which this data constructor
     is associated) and a [datacon_info] record. *)
  datacons: ('v var * datacon_info) D.global_env;

  (* The name of the current module. *)
  module_name: Module.name;

  (* The current start and end positions. *)
  location: location;

}

(* ---------------------------------------------------------------------------- *)

(* Error messages. *)

type error =
  | Unbound of (* namespace: *) string * (* name: *) string
  | BoundTwice of (* namespace: *) string * (* name: *) string
  | Mismatch of (* expected: *) kind * (* inferred: *) kind
  | ArityMismatch of (* expected: *) int * (* provided: *) int
  | ModeConstraintMismatch of (* provided: *) kind
  | IllegalConsumes
  | BadHypothesisInFact
  | BadConclusionInFact of (* data type constructor: *) Variable.name * (* parameters: *) Variable.name list
  | NonDistinctHeadsInFact of Variable.name * Mode.mode
  | DuplicateField of Variable.name
  | AdopterNotExclusive of Variable.name
  | FieldMismatch of Datacon.name * Field.name list (* missing fields *) * Field.name list (* extra fields *)
  | ImplicationOnlyOnArrow

exception KindError of (Buffer.t -> unit -> unit)

module P = struct

  open MzPprint

  let print_var (v : 'v var) : string =
    match v with
    | Local level ->
	Printf.sprintf "level = %d" level
    | NonLocal _ ->
	"external point"

  let print_env (env : 'v env) : document =
    (* We print just [env.variables]. *)
    V.print_global_env (fun (v, kind) ->
      string "kind = " ^^ print_kind kind ^^ string ", " ^^ string (print_var v)
    ) env.variables

  let print_field field =
    utf8string (Field.print field)

  let print_fields fields =
    separate_map (comma ^^ space) print_field fields

  let p_fields buf fields =
    pdoc buf (print_fields, fields)

end

let is_dummy_location (sp, _) =
  sp == Lexing.dummy_pos

let print_error env error buf () =
  let bprintf s = Printf.bprintf buf s in
  (* Print the location, unless it is a dummy location (it should not be). *)
  if not (is_dummy_location env.location) then
    Lexer.p buf env.location;
  (* Print the error message. *)
  begin match error with
  | Unbound (namespace, x) ->
      bprintf
	"The %s %s has not been defined."
	namespace x
  | BoundTwice (namespace, x) ->
      bprintf
        "The %s %s is defined twice."
        namespace x
  | Mismatch (expected, inferred) ->
      let il, ir = Kind.as_arrow inferred in
      let xl, xr = Kind.as_arrow expected in
      (* The expected kind is never an arrow. *)
      assert (xl = []);
      if Kind.equal ir xr then begin
	let missing = List.length il in
	assert (missing <> 0);
	(* Only a type variable can have an arrow kind; a type application
	   cannot. So the number of arguments supplied by the user must be
	   zero, and we can print "expects %d arguments" as opposed to the
	   less precise "expects %d more arguments". *)
        bprintf
          "This type constructor expects %d argument%s."
          missing
	  (if missing > 1 then "s" else "")
      end
      else
        bprintf
          "This type has kind %s, whereas a type of kind %s was expected."
          (print ir)
          (print xr)
  | ArityMismatch (expected, provided) ->
      bprintf
        "This type expects %d parameter%s, but is applied to %d argument%s."
        expected (MzPprint.plural expected)
	provided (MzPprint.plural provided)
  | ModeConstraintMismatch inferred ->
      bprintf
	"This type has kind %s, whereas a type of kind type or perm was expected."
        (print inferred)
  | IllegalConsumes ->
      bprintf
        "The consumes keyword is not allowed here."
  | BadHypothesisInFact ->
      bprintf
        "An assumption in a fact must bear on a type variable."
  | BadConclusionInFact (x, args) ->
      let expected =
	List.fold_left (fun accu arg ->
	  accu ^ " " ^ Variable.print arg
	) (Variable.print x) args
      in
      bprintf
        "The conclusion of this fact must bear on the type %s."
        expected
  | NonDistinctHeadsInFact (x, mode) ->
      bprintf
	"Distinct facts must concern distinct modes.\n\
         In the declaration of %a, two distinct facts concern the mode %s"
	Variable.p x
	(Mode.print mode)
  | DuplicateField d ->
      bprintf
        "The field %a appears several times in this branch"
        Variable.p d
  | AdopterNotExclusive x ->
      bprintf
        "Type %a carries an adopts clause, but is not marked as mutable"
        Variable.p x
  | FieldMismatch (datacon, missing, extra) ->
      bprintf
        "This type does not have the fields of data constructor %a"
        Datacon.p datacon;
      if missing <> [] then
	bprintf
	  "\nThe following field%s missing: %a"
	  (if List.length missing > 1 then "s are" else " is")
	  P.p_fields missing;
      if extra <> [] then
	bprintf
	  "\nThe following field%s superfluous: %a"
	  (if List.length extra > 1 then "s are" else " is")
	  P.p_fields extra
  | ImplicationOnlyOnArrow ->
      bprintf
	"Implication => is permitted only on top of a function type."
  end;
  if Log.debug_level () > 4 then begin
    Printf.bprintf buf "\n";
    MzPprint.pdoc buf (P.print_env, env)
  end
;;

let raise_error env e =
  raise (KindError (print_error env e))

let unbound namespace print env x =
  raise_error env (Unbound (namespace, print_maybe_qualified print x))

let bound_twice namespace print env x =
  raise_error env (BoundTwice (namespace, print x))

let mismatch env expected_kind inferred_kind =
  raise_error env (Mismatch (expected_kind, inferred_kind))

let illegal_consumes env =
  raise_error env IllegalConsumes

let non_distinct_heads_in_fact env x mode =
  raise_error env (NonDistinctHeadsInFact (x, mode))
;;

let bad_conclusion_in_fact env x args =
  raise_error env (BadConclusionInFact (x, args))
;;

let duplicate_field env f =
  raise_error env (DuplicateField f)
;;

let field_mismatch env dc missing extra =
  raise_error env (FieldMismatch (dc, missing, extra))

let implication_only_on_arrow env =
  raise_error env ImplicationOnlyOnArrow

(* ---------------------------------------------------------------------------- *)

(* Provided we have the name of a data constructor, its index, and the ordered
   list of its fields, we can create a [datacon_info] record. *)

let mkdatacon_info dc i fields = {
  datacon_name = Datacon.print dc;
  datacon_arity = List.length fields;
  datacon_index = i;
  datacon_fields =
    let open Field.Map in
    MzList.fold_lefti (fun i accu f -> add f i accu) empty fields;
}

(* ---------------------------------------------------------------------------- *)

(* An empty environment. *)

let empty module_name = {
  level = 0;
  variables = V.empty;
  datacons = D.empty;
  module_name;
  location = dummy_loc;
}

(* A so-called initial environment can be constructed by populating an empty
   environment with qualified names of variables and data constructors. They
   represent names that have been defined in a module other than the current
   module. *)

(* TEMPORARY this approach seems inelegant and should ideally be abandoned in
   the future *)

let initial
  (module_name : Module.name)
  (names : (Module.name * Variable.name * kind * 'v) list)
  (datacons : (Module.name * 'v * int * Datacon.name * Field.name list) list)
: 'v env =

  let variables =
    List.fold_left (fun accu (m, x, kind, v) ->
      V.extend_qualified m x (NonLocal v, kind) accu
    ) V.empty names

  and datacons =
    List.fold_left (fun accu (m, var, i, dc, fields) ->
      let info = mkdatacon_info dc i fields in
      D.extend_qualified m dc (NonLocal var, info) accu
    ) D.empty datacons
  in

  { (empty module_name) with variables; datacons }

(* ---------------------------------------------------------------------------- *)

(* Working with environments *)

let location env =
  env.location

let module_name env =
  env.module_name

(* [find env x] looks up the possibly-qualified name [x] in the environment [env]. *)
let find env x : 'v var * kind =
  try
    V.lookup_maybe_qualified x env.variables
  with Not_found ->
    unbound "variable" Variable.print env x

let find_kind env x : kind =
  let _, kind = find env x in
  kind

(* This version of [find_var] is for internal use; it returns a de-Bruijn-level
   [var]. Further on, we compose it with [level2index]. *)
let find_var env x : 'v var =
  let v, _ = find env x in
  v

(* [level2index] converts a de-Bruijn-level [var] to a de-Bruijn-index [var]. *)
let level2index env = function
  | Local level ->
      Local (env.level - level - 1)
  | NonLocal _ as v ->
      v

let find_datacon env (datacon : Datacon.name maybe_qualified) : 'v var * datacon_info =
  try
    D.lookup_maybe_qualified datacon env.datacons
  with Not_found ->
    unbound "data constructor" Datacon.print env datacon

(* ---------------------------------------------------------------------------- *)

(* [bind env (x, kind)] binds the name [x] with kind [kind]. *)
let bind env (x, kind) : 'v env =
  (* The current level becomes [x]'s level. The current level is
     then incremented. *)
  { env with
    level = env.level + 1;
    variables = V.extend_unqualified x (Local env.level, kind) env.variables }
;;

let bind_external env (x, kind, p) : 'v env =
  { env with variables = V.extend_unqualified x (NonLocal p, kind) env.variables }
;;

(* [dc] is the unqualified data constructor, [v] is the data type
   that it is associated with. *)
let bind_datacon env dc (v : 'v var) info =
  { env with datacons = D.extend_unqualified dc (v, info) env.datacons }
;;

(* Bind all the data constructors from a data type group *)
let bind_datacons env data_type_group =
  List.fold_left (fun env -> function
    | Concrete (_, (name, _), rhs, _) ->
        (* TEMPORARY why Unqualified? no risk of masking? *)
        let v : 'v var = find_var env (Unqualified name) in
        MzList.fold_lefti (fun i env (dc, fields) ->
          (* We're building information for the interpreter: drop the
           * permission fields. *)
          let fields = MzList.map_some (function
            | FieldValue (name, _) -> Some name
            | FieldPermission _ -> None
          ) fields in
          bind_datacon env dc v (mkdatacon_info dc i fields)
        ) env rhs
    | Abbrev _
    | Abstract _ ->
        env
  ) env data_type_group
;;

(* Find in [tsenv.env] all the names exported by module [mname], and add them to our
 * own [tsenv]. *)
let open_module_in (m : Module.name) (env : 'v env) : 'v env =
  (* Unqualify the variables and data constructors qualified with [m]. *)
  (* The call to [freeze] is just a way of avoiding the failure
     in [unqualify] if this module does not exist, i.e. it exports
     no variables or no data constructors. We could potentially
     perform this [freeze] earlier, i.e. when the module is constructed,
     not when it is opened. *)
  { env with
    variables = V.unqualify m (V.freeze m env.variables);
    datacons = D.unqualify m (D.freeze m env.datacons);
  }

(* [locate env p] updates [env] with the provided location information. *)
let locate env location =
  { env with location }

(* [extend env xs] extends the current environment with a lsit of new bindings. *)
let extend env (xs : type_binding list) : 'v env =
  List.fold_left (fun env (x, k, _) ->
    bind env (x, k)
  ) env xs
;;

(* ---------------------------------------------------------------------------- *)

(* Yes, this is a bit too abstract and contrived, sorry. I want to
   avoid using generic hashing & equality over an abstract type of
   names. *)

let check_for_duplicate_things
    (compare : 'thing -> 'thing -> int)
    (project : 'a -> 'thing)
    (elements: 'a list)
    (exit: 'thing -> 'b)
    : unit
=
  let compare (x : 'a) (y : 'a) : int =
    compare (project x) (project y)
  in
  match MzList.check_for_duplicates compare elements with
  | None ->
      ()
  | Some (x, _) ->
      exit (project x)

let check_for_duplicate_variables
    (project : 'a -> Variable.name)
    (elements: 'a list)
    (exit: Variable.name -> 'b)
    : unit
=
  check_for_duplicate_things Variable.compare project elements exit

let check_for_duplicate_bindings env bindings = (* TEMPORARY isn't this check performed in too many places? *)
  check_for_duplicate_variables
    (fun (x, _) -> x)
    bindings
    (fun x -> bound_twice "variable" Variable.print env x)

let check_for_duplicate_datacons
    (project : 'a -> Datacon.name)
    (elements: 'a list)
    (exit: Datacon.name -> 'b)
    : unit
=
  check_for_duplicate_things Datacon.compare project elements exit

(* ---------------------------------------------------------------------------- *)

(* The ↑ relation, which we implement as [names]. *)

(* [bv loc accu p] adds to the accumulator [accu] the names bound by the
   pattern [p]. For each name, we add a triple of the name, its kind (which is
   always [KTerm]), and a location. *)

let rec bv loc (accu : type_binding list) (p : pattern) : type_binding list =
  match p with
  | PVar x ->
      (x, KTerm, loc) :: accu
  | PTuple ps ->
      List.fold_left (bv loc) accu ps
  | PConstruct (_, fps) ->
      List.fold_left (fun accu (_, p) ->
	bv loc accu p
      ) accu fps
  | PLocated (p, loc) ->
      bv loc accu p
  | PConstraint (p, _) ->
      bv loc accu p
  | PAs (p, x) ->
      (x, KTerm, loc) :: bv loc accu p
  | PAny ->
      accu

(* [names ty] returns a list of the names that [ty] binds. We check
   that these names are distinct, so their order is irrelevant. *)

(* In principle, the type [ty] should have kind [type], but during kind-checking,
   [names] can be called before we have ensured that this is the case. *)

let names env ty : type_binding list =

  (* First, convert the type [ty] to a pattern, using the function
     [type_to_pattern]. This function is also used by the interpreter
     and compiler, so we should have a unified notion of which names
     are ghost and which names are actually available at runtime. *)

  let p = type_to_pattern ty in

  (* Now, collect the names bound by [p]. *)

  let bindings = bv env.location [] p in

  (* Check that no name is bound twice. *)

  (* TEMPORARY this is almost check_for_duplicate_bindings *)
  check_for_duplicate_variables
    (fun (x, _, _) -> x)
    bindings
    (fun x -> bound_twice "variable" Variable.print env x);

  (* Return the bindings. *)
  bindings
;;

let reset env ty =
  extend env (names env ty)

(* [bindings_data_type_group] returns a list of names that the whole data type
   group binds, with the corresponding kinds. The list is in the same order as
   the data type definitions. *)
let bindings_data_type_group (data_type_group: data_type_def list): (Variable.name * kind) list =
  List.map (function
    | Concrete (_flag, (name, params), _, _) ->
        let params = List.map (fun (_, (x, y, _)) -> x, y) params in
        let k = karrow params KType in
        (name, k)
    | Abbrev ((name, params), return_kind, _)
    | Abstract ((name, params), return_kind, _) ->
        let params = List.map (fun (_, (x, y, _)) -> x, y) params in
        let k = karrow params return_kind in
        (name, k)
  ) data_type_group
;;


(* [bindings_pattern] returns in prefix order the list of names bound in a
   pattern. *)
let bindings_pattern (p: pattern) : (Variable.name * kind) list =
  let loc = (Lexing.dummy_pos, Lexing.dummy_pos) in
  let bindings = bv loc [] p in
  (* Discard the dummy location information, and reverse the list, so it
     appears in left-to-right order (not sure if it's important). *)
  List.rev_map (fun (x, kind, _) -> x, kind) bindings
;;

(* [bindings_patterns] is the same, but applies to a list of patterns.
   The check for duplicates (if performed) applies to all patterns at
   once. *)
let bindings_patterns (ps: pattern list) : (Variable.name * kind) list =
  bindings_pattern (PTuple ps)

(* ---------------------------------------------------------------------------- *)

(* The kind-checking functions. *)


(* This just makes sure that the type parameters mentioned in the fact are in
   the list of the original type parameters. *)
let rec check_fact_parameter env (args: Variable.name list) (t: typ) =
  match t with
  | TyLocated (t, p) ->
      check_fact_parameter (locate env p) args t
  | TyVar (Unqualified x) when List.exists (Variable.equal x) args ->
      ()
  | _ ->
      raise_error env BadHypothesisInFact

(* The conclusion of a fact, if any, must be the exact original type applied to
   the exact same arguments. *)
let rec check_fact_conclusion env (tc: Variable.name) (args: Variable.name list) (t: typ) =
  match t with
  | TyLocated (t, p) ->
      check_fact_conclusion (locate env p) tc args t
  | _ ->
      match flatten_tyapp t with
      | TyVar (Unqualified x'), args' ->
          Log.debug "%a %a" Variable.p tc Variable.p x';
          if not (Variable.equal tc x') then
            bad_conclusion_in_fact env tc args;
          if not (List.length args = List.length args') then
            bad_conclusion_in_fact env tc args;
          List.iter2 (fun x arg' ->
            match arg' with
            | TyVar (Unqualified x')
            | TyLocated (TyVar (Unqualified x'), _) ->
                if not (Variable.equal x x') then
                  bad_conclusion_in_fact env tc args;
            | _ ->
                bad_conclusion_in_fact env tc args) args args';
      | _ ->
          bad_conclusion_in_fact env tc args;
;;

let check_distinct_heads env name facts =
  ignore (
    List.fold_left (fun accu (Fact (_, (mode, _))) ->
      if Mode.ModeMap.mem mode accu then
	non_distinct_heads_in_fact env name mode
      else
	Mode.ModeMap.add mode () accu
    ) Mode.ModeMap.empty facts
  )

let rec check env (ty : typ) (expected : kind) =
  match ty with

  (* Treating the following cases here may seem redundant, but allows us to
     detect a mismatch between inferred and expected kinds at a deeper
     location, leading to a better error message. *)

  | TyLocated (ty, loc) ->
      check (locate env loc) ty expected

  | TyConsumes ty ->
      check env ty expected

  (* The general case. *)

  | _ ->
      let inferred = infer env ty in
      if not (Kind.equal inferred expected) then
	mismatch env expected inferred

and infer env (ty : typ) : kind =
  match ty with

  | TyLocated (ty, loc) ->
      infer (locate env loc) ty

  | TyConsumes ty ->
      infer env ty

  | TyTuple tys ->
      List.iter (fun ty -> check env ty KType) tys;
      KType

  | TyUnknown ->
      KType

  | TyDynamic ->
      KType

  | TyEmpty ->
      KPerm

  | TyVar x ->
      find_kind env x

  | TyConcrete (branch, clause) ->
      (* TEMPORARY parts of the checks are performed later, in [TransSurface]. Why? *)
      check_branch env branch;
      Option.iter (fun ty -> check_reset env ty KType) clause;
      KType

  | TySingleton ty ->
      check env ty KTerm; (* [reset] irrelevant *)
      KType

  | TyApp (ty1, ty2s) ->
      let kind1 = infer env ty1 in (* [reset] irrelevant *)
      let kind2s, kind = as_arrow kind1 in
      let expected = List.length kind2s
      and provided = List.length ty2s in
      if expected <> provided then
	raise_error env (ArityMismatch (expected, provided));
      List.iter2 (check_reset env) ty2s kind2s;
      kind

  | TyArrow (ty1, ty2) ->
      (* The scope of the names introduced in the left-hand side
	 extends to the left- and right-hand sides. *)
      let env = reset env ty1 in
      check env ty1 KType;
      check_reset env ty2 KType;
      KType

  | TyForall ((x, kind, _), ty)
  | TyExists ((x, kind, _), ty) ->
      let env = bind env (x, kind) in
      check_reset env ty KType;
      KType

  | TyAnchoredPermission (ty1, ty2) ->
      check env ty1 KTerm;  (* [reset] irrelevant *)
      check_reset env ty2 KType;
      KPerm

  | TyStar (ty1, ty2) ->
      check env ty1 KPerm; (* [reset] irrelevant *)
      check env ty2 KPerm; (* [reset] irrelevant *)
      KPerm

  | TyNameIntro (x, ty) ->
      (* In principle, this name has already been bound in the
	 environment, via a previous call to [reset]. *)
      assert (find_kind env (Unqualified x) = KTerm);
    check env ty KType;
    KType

  | TyBar (t1, t2) ->
      check env t1 KType;
      check env t2 KPerm; (* [reset] irrelevant *)
      KType

  | TyAnd (c, ty)
  | TyImply (c, ty) ->
      check_mode_constraint env c;
      check env ty KType;
      KType

and check_mode_constraint env (_, ty) =
  match infer_reset env ty with
  | KType
  | KPerm ->
      ()
  | inferred ->
      raise_error env (ModeConstraintMismatch inferred)

and check_field env (field : data_field_def) =
  match field with
  | FieldValue (_, ty) ->
      check_reset env ty KType
  | FieldPermission t ->
      check env t KPerm (* [reset] irrelevant *)

and check_branch: 'a. 'v env -> ('a * data_field_def list) -> unit = fun env branch ->
  let _, fields = branch in
  let names = MzList.map_some (function
    | FieldValue (name, _) ->
        Some name
    | FieldPermission _ ->
        None
  ) fields in
  check_for_duplicate_variables
    (fun x -> x)
    names
    (duplicate_field env);
  List.iter (check_field env) fields

and infer_reset env ty =
  infer (reset env ty) ty

and check_reset env ty expected =
  check (reset env ty) ty expected

(* Check a data type definition. For abstract types, this just checks that the
   fact is well-formed. For concrete types, check that the branches are all
   well-formed. *)
let check_data_type_def env (def: data_type_def) =
  match def with
  | Abstract ((name, bindings), _return_kind, facts) ->
      (* Get the names of the parameters. *)
      let args = List.map (fun (_, (x, _, _)) -> x) bindings in
      (* Perform a tedious check. *)
      List.iter (function Fact (clauses, conclusion) ->
        List.iter (fun (_, t) -> check_fact_parameter env args t) clauses;
        let (_, t) = conclusion in check_fact_conclusion env name args t
      ) facts;
      check_distinct_heads env name facts
  | Concrete (flavor, (name, bindings), branches, clause) ->
      let bindings = List.map (fun (_, (x, y, _)) -> x, y) bindings in
      let env = List.fold_left bind env bindings in
      (* Check the branches. *)
      List.iter (check_branch env) branches;
      begin match clause with
      | None ->
          ()
      | Some t ->
          check_reset env t KType;
          (* We can do that early. *)
	  if not (DataTypeFlavor.can_adopt flavor) then
	    raise_error env (AdopterNotExclusive name)
      end
  | Abbrev ((_, bindings), return_kind, t) ->
      let bindings = List.map (fun (_, (x, y, _)) -> x, y) bindings in
      let env = List.fold_left bind env bindings in
      check_reset env t return_kind
;;


let check_data_type_group env (data_type_group: data_type_def list) =
  (* Check that the constructors are unique to this data type group. *)
  let all_branches = MzList.map_flatten (function
    | Abbrev _
    | Abstract _ ->
        []
    | Concrete (_, _, branches, _) ->
        branches
  ) data_type_group in
  check_for_duplicate_datacons
    (fun (datacon, _fields) -> datacon)
    all_branches
    (bound_twice "data constructor" Datacon.print env);

  (* Do the remainder of the checks. *)
  List.iter (check_data_type_def env) data_type_group
;;


let rec check_pattern env (pattern: pattern) =
  match pattern with
  | PConstraint (p, t) ->
      check_pattern env p;
      check_reset env t KType
  | PVar x ->
      assert (find_kind env (Unqualified x) = KTerm)
  | PTuple patterns ->
      List.iter (check_pattern env) patterns
  | PConstruct (_, name_pats) ->
      let _, patterns = List.split name_pats in
      List.iter (check_pattern env) patterns
  | PLocated (p, _) ->
      check_pattern env p
  | PAs (p1, x2) ->
      check_pattern env p1;
      check_pattern env (PVar x2)
  | PAny ->
      ()
;;


let rec check_patexpr env (flag: rec_flag) (pat_exprs: (pattern * expression) list): 'v env =
  let patterns, expressions = List.split pat_exprs in
  (* Introduce all bindings from the patterns *)
  let bindings = bindings_patterns patterns in
  check_for_duplicate_bindings env bindings;
  let sub_env = List.fold_left bind env bindings in
  (* Type annotation in patterns may reference names introduced in the entire
   * pattern (same behavior as tuple types). *)
  List.iter (check_pattern sub_env) patterns;
  (* Whether the variables defined in the pattern are available in the
   * expressions depends, of course, on whether this is a recursive binding. *)
  begin match flag with
  | Recursive ->
      List.iter (check_expression sub_env) expressions
  | Nonrecursive ->
      List.iter (check_expression env) expressions
  end;
  (* Return the environment extended with bindings so that we can check whatever
   * comes afterwards. *)
  sub_env


and check_expression env (expr: expression) =
  match expr with
  | EConstraint (e, t) ->
      check_expression env e;
      check_reset env t KType

  | EVar x ->
      let k = find_kind env x in
      (* TEMPORARY check that only lambda-bound variables can appear in code *)
      if k <> KTerm then
        mismatch env KTerm k

  | EBuiltin _ ->
      ()

  | ELet (flag, pat_exprs, expr) ->
      let env = check_patexpr env flag pat_exprs in
      check_expression env expr

  | EFun (bindings, arg, return_type, body) ->
      check_for_duplicate_variables Types.fst3 bindings (bound_twice "variable" Variable.print env);
      let bindings = List.map (fun (x, y, _) -> x, y) bindings in
      let env = List.fold_left bind env bindings in
      let env = reset env arg in
      check env arg KType;
      check_expression env body;
      check_reset env return_type KType

  | EAssign (e1, _, e2) ->
      check_expression env e1;
      check_expression env e2

  | EAssignTag (e1, _, _) ->
      check_expression env e1

  | EAccess (e, _) ->
      check_expression env e

  | EAssert t ->
      check env t KPerm (* [reset] irrelevant *)

  | EApply (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | ETApply (e, args) ->
      List.iter (check_tapp env) args;
      check_expression env e

  | EMatch (_, e, pat_exprs) ->
      check_expression env e;
      List.iter (fun (pat, expr) ->
        let bindings = bindings_pattern pat in
	check_for_duplicate_bindings env bindings;
        let sub_env = List.fold_left bind env bindings in
        check_pattern sub_env pat;
        check_expression sub_env expr
      ) pat_exprs

  | ETuple exprs ->
      List.iter (check_expression env) exprs

  | EConstruct (_, field_exprs) ->
      (* TEMPORARY datacon is not checked here! *)
      let _, exprs = List.split field_exprs in
      List.iter (check_expression env) exprs

  | EIfThenElse (_, e1, e2, e3) ->
      check_expression env e1;
      check_expression env e2;
      check_expression env e3

  | ESequence (e1, e2)
  | EGive (e1, e2)
  | ETake (e1, e2)
  | EOwns (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | ELocated (e, p) ->
      check_expression (locate env p) e

  | EInt _ ->
      ()

  | EExplained e ->
      check_expression env e


  | EFail ->
      ()

and check_tapp env = function
  | Ordered ty
  | Named (_, ty) ->
      ignore (infer_reset env ty)

;;


(* Because the binding structure of top-level declarations is possibly
 * complicated, because of patterns, this function does both the binding and the
 * checking at the same time (i.e. there's no [bindings_declaration_group]
 * function. However, it returns the environment with all the bindings added. *)
let check_declaration_group env = function
  | DLocated (DMultiple (rec_flag, pat_exprs), p) ->
    let env = locate env p in
    check_patexpr env rec_flag pat_exprs
  | _ ->
      Log.error "Unexpected shape for a [declaration_group]."
;;

let check_implementation env (program: implementation) : unit =
  let (_ : 'v env) = List.fold_left (fun env -> function
    | DataTypeGroup (loc, rec_flag, data_type_group) ->
        (* Collect the names from the data type definitions, since they
         * will be made available in both the data type definitions themselves,
         * and the value definitions. All definitions in a data type groupe are
         * mutually recursive. *)
        let bindings = bindings_data_type_group data_type_group in
        check_for_duplicate_bindings env bindings;
        (* Create an environment that includes those names. *)
        let env = locate env loc in
        let extended_env = List.fold_left bind env bindings in
	(* Also include the data constructors. *)
	let extended_env = bind_datacons extended_env data_type_group in
        (* Check the data type definitions in the appropriate environment. *)
	let appropriate_env =
	  match rec_flag with
	  | Nonrecursive -> env
	  | Recursive -> extended_env
	in
	check_data_type_group appropriate_env data_type_group;
	(* Return the extended environment. *)
        extended_env
	  (* TEMPORARY there is code duplication between here and
	     [TransSurface.translate_data_type_group] *)

    | ValueDeclarations declaration_group ->
        (* This function does everything at once and takes care of both binding
         * the variables and checking the bodies. *)
        check_declaration_group env declaration_group;

    | PermDeclaration (x, t) ->
        check_reset env t KType;
        bind env (x, KTerm)

    | OpenDirective mname ->
        open_module_in mname env
  ) env program in
  ()
;;

let check_interface env (interface: interface) =
  (* Check for duplicate variables. A variable cannot be declared twice
     in an interface file. *)
  let all_bindings = MzList.map_flatten (function
    | DataTypeGroup (_, _, data_type_group) ->
        bindings_data_type_group data_type_group
    | PermDeclaration (x, _) ->
        [x, KTerm]
    | OpenDirective _ ->
        []
    | ValueDeclarations _ ->
        assert false
  ) interface in
  check_for_duplicate_variables fst all_bindings (bound_twice "variable" Variable.print env);
    (* TEMPORARY this results in a dummy location *)

  (* Check for duplicate data constructors. A data constructor cannot be
     declared twice in an interface file. *)
  let all_datacons = MzList.map_flatten (function
    | DataTypeGroup (_, _, data_type_group) ->
        MzList.map_flatten (function
          | Abbrev _
          | Abstract _ ->
              []
          | Concrete (_, _, branches, _) ->
              branches
        ) data_type_group
    | _ ->
        []
  ) interface in
  check_for_duplicate_datacons fst all_datacons (bound_twice "data constructor" Datacon.print env);
    (* TEMPORARY this results in a dummy location *)

  (* Do all the regular checks. *)
  check_implementation env interface
;;

(* Redefine [find_var] and [find_datacon] for public use. *)
let find_var env x =
  level2index env (find_var env x)

let find_datacon env datacon =
  let v, info = find_datacon env datacon in
  level2index env v, info

(* Rename [check_reset] and [infer_reset] for public use. *)
let check =
  check_reset

let infer =
  infer_reset

