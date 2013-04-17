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
module T = TypeCore
module E = Expressions

(* ---------------------------------------------------------------------------- *)

(* A local identifier (one that is defined in the current module) is represented
   as a de Bruijn level (not to be confused with a de Bruijn index!). This is an
   implementation detail of [KindCheck] and does not affect its clients. *)

type level =
    int

(* An external identifier (one that is defined in another module) is represented
   as a variable of type [TypeCore.var]. Think of it as a binder that has been
   opened already. *)

(* Thus, for our purposes, a [var] is either a local name or a non-local name. *)

type var =
       Local of level
  | NonLocal of T.var

(* These data structures are used to keep track of the known variables and data
   constructors. *)

module V =
  Namespace.MakeNamespace(Variable)

module D =
  Namespace.MakeNamespace(Datacon)

(* The environments defined here are used for kind checking and for translating
   types down to the core syntax. *)

type env = {

  (* The current de Bruijn level. *)
  level: level;

  (* A mapping of (qualified or unqualified) variable names to pairs of a kind
     and a variable. *)
  variables: (kind * var) V.global_env;

  (* A mapping of (qualified or unqualified) data constructor names to... well,
     for now, we keep a variable (the algebraic data type with which this data
     constructor is associated) and a [datacon_info] record. TEMPORARY maybe we
     could simplify this? The physical identity of the [datacon_info] records
     matters (there must be one record per data constructor, no more). *)
  datacons: (var * datacon_info) D.global_env;

  (* The name of the current module. Not relevant for us, but this is used by
     the function [TransSurface.name_user]. TEMPORARY? *)
  module_name: Module.name;

  (* The current start and end positions. *)
  location: location;

}

(* ---------------------------------------------------------------------------- *)

let mkdatacon_info dc i fields =
  (* Create the map. *)
  let fmap = MzList.fold_lefti
    (fun i fmap f -> Field.Map.add f i fmap)
    Field.Map.empty fields
  in {
    datacon_name = Datacon.print dc;
    datacon_arity = List.length fields;
    datacon_index = i;
    datacon_fields = fmap;
  }
;;


(* The initial environment. *)

  (* [Driver] already discovered our dependencies for us, and processed them, so
   * [env] contains all the information about our dependencies. However, it
   * contains no information about the module that's being processed, except
   * for the field [module_name] (that's not entirely true if we're matching an
   * implementation against its interface but the bottom line is: only use this
   * environment for your dependencies on other modules). *)
  
let initial (env: T.env): env =

  (* TEMPORARY comment *)
  let variables =
    List.fold_left (fun accu (m, x, kind, v) ->
      V.extend_qualified m x (kind, NonLocal v) accu
    ) V.empty (T.get_external_names env)
  in

  (* Build a table of the initially available data constructors: these are
     the data constructors that exist in [env] and have been defined in a
     module other than the current module. They are accessible via their
     qualified name. *)
  let datacons =
    let open T in
    fold_external_datacons env (fun accu mname var i branch ->
      let dc = branch.branch_datacon
      and fields = branch.branch_fields in
      (* Drop the permission fields. *)
      let fields = MzList.map_some (function
	| FieldValue (name, _) -> Some name
	| FieldPermission _ -> None
      ) fields in
      let info = mkdatacon_info dc i fields in
      D.extend_qualified mname dc (NonLocal var, info) accu
    ) D.empty
  in {
    level = 0;
    variables;
    datacons;
    module_name = T.module_name env;
    location = dummy_loc;
  }

(* ---------------------------------------------------------------------------- *)

(* Error messages. *)

type error = env * raw_error

and raw_error =
  | Unbound of string
  | Mismatch of kind * kind
  | ArityMismatch of (* expected: *) int * (* provided: *) int
  | BoundTwice of Variable.name
  | IllegalConsumes
  | BadConditionsInFact of Variable.name
  | BadConclusionInFact of Variable.name
  | NonDistinctHeadsInFact of Variable.name * Mode.mode
  | DuplicateConstructor of Datacon.name
  | DuplicateField of Variable.name
  | AdopterNotExclusive of Variable.name
  | UnboundDataConstructor of Datacon.name
  | FieldMismatch of Datacon.name * Field.name list (* missing fields *) * Field.name list (* extra fields *)
  | ImplicationOnlyOnArrow

exception KindError of error

let raise_error env e =
  raise (KindError (env, e))
;;

module P = struct

  open MzPprint

  let print_var (v : var) : string =
    match v with
    | Local level ->
	Printf.sprintf "level = %d" level
    | NonLocal _ ->
	"external point"

  let print_env (env : env) : document =
    (* We print just [env.variables]. *)
    V.print_global_env (fun (kind, v) ->
      string "kind = " ^^ print_kind kind ^^ string ", " ^^ string (print_var v)
    ) env.variables

  let print_field field =
    utf8string (Field.print field)

  let print_fields fields =
    separate_map (comma ^^ space) print_field fields

  let p_fields buf fields =
    Types.TypePrinter.pdoc buf (print_fields, fields)

end

let print_error buf (env, raw_error) =
  let open Types.TypePrinter in
  let bprintf s = Printf.bprintf buf s in
  (* Print the location. *)
  Lexer.p buf env.location;
  (* Print the error message. *)
  begin match raw_error with
  | Unbound x ->
      bprintf "Unbound identifier: %s" x
  | Mismatch (expected_kind, inferred_kind) ->
      let _, inferred = Kind.as_arrow inferred_kind in
      let _, expected = Kind.as_arrow expected_kind in
      if inferred <> expected then
        bprintf
          "This is a %a but we were expecting a %a"
          p_kind inferred
          p_kind expected
      else
        bprintf
          "This type has kind %a but we were expecting kind %a"
          p_kind inferred_kind
          p_kind expected_kind
  | ArityMismatch (expected, provided) ->
      bprintf
        "This type expects %d parameter%s, but is applied to %d argument%s."
        expected (MzPprint.plural expected)
	provided (MzPprint.plural provided)
  | BoundTwice x ->
      bprintf
        "Variable %a is bound twice"
        Variable.p x
  | IllegalConsumes ->
      bprintf
        "Unexpected consumes annotation"
  | BadConditionsInFact x ->
      bprintf
        "The conditions for the fact about %a can only be type variables"
        Variable.p x
  | BadConclusionInFact x ->
      bprintf
        "The conclusion for the fact about %a can only be %a applied to its \
        parameters"
        Variable.p x
        Variable.p x
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
   | DuplicateConstructor d ->
      bprintf
        "The constructor %a appears several times in this data type group"
        Datacon.p d
  | AdopterNotExclusive x ->
      bprintf
        "Type %a carries an adopts clause, but is not marked as mutable"
        Variable.p x
  | UnboundDataConstructor d ->
      bprintf
        "Unknown data constructor: %a"
        Datacon.p d
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
    Types.TypePrinter.pdoc buf (P.print_env, env)
  end
;;

let unbound env x =
  raise_error env (Unbound x)
;;

let mismatch env expected_kind inferred_kind =
  raise_error env (Mismatch (expected_kind, inferred_kind))
;;

let illegal_consumes env =
  raise_error env IllegalConsumes
;;

let bound_twice env x =
  raise_error env (BoundTwice x)
;;

let bad_condition_in_fact env x =
  raise_error env (BadConditionsInFact x)
;;

let non_distinct_heads_in_fact env x mode =
  raise_error env (NonDistinctHeadsInFact (x, mode))
;;

let bad_conclusion_in_fact env x =
  raise_error env (BadConclusionInFact x)
;;

let duplicate_constructor env d =
  raise_error env (DuplicateConstructor d)
;;

let duplicate_field env f =
  raise_error env (DuplicateField f)
;;

let field_mismatch env dc missing extra =
  raise_error env (FieldMismatch (dc, missing, extra))

let implication_only_on_arrow env =
  raise_error env ImplicationOnlyOnArrow

(* ---------------------------------------------------------------------------- *)

(* Working with environments *)

let location env =
  env.location

let module_name env =
  env.module_name

(* [find env x] looks up the possibly-qualified name [x] in the environment [env]. *)
let find env x : kind * var =
  try
    V.lookup_maybe_qualified x env.variables
  with Not_found ->
    unbound env (print_maybe_qualified Variable.print x)

let find_kind env x : kind =
  let kind, _ = find env x in
  kind

let find_var env x : var =
  let _, v = find env x in
  v

(* [level2index] converts a de Bruijn level to a de Bruijn index. *)
let level2index env level =
  env.level - level - 1

(* [tvar v env] transforms the variable [v] into a type variable
   in the internal syntax. *)
let tvar env v : T.typ =
  match v with
  |    Local level -> T.TyBound (level2index env level)
  | NonLocal v     -> T.TyOpen v

(* [evar v env] transforms the variable [v] into an expression variable
   in the internal syntax. *)
let evar env v =
  match v with
  |    Local level -> E.EVar (level2index env level)
  | NonLocal v     -> E.EOpen v

(* [bind env (x, kind)] binds the name [x] with kind [kind]. *)
let bind env (x, kind) : env =
  (* The current level becomes [x]'s level. The current level is
     then incremented. *)
  { env with
    level = env.level + 1;
    variables = V.extend_unqualified x (kind, Local env.level) env.variables }
;;

let bind_external env (x, kind, p) : env =
  { env with variables = V.extend_unqualified x (kind, NonLocal p) env.variables }
;;

(* [dc] is the unqualified data constructor, [v] is the data type
   that it is associated with. *)
let bind_datacon env dc (v : var) info =
  { env with datacons = D.extend_unqualified dc (v, info) env.datacons }
;;

(* Bind all the data constructors from a data type group *)
let bind_datacons env data_type_group =
  List.fold_left (fun env -> function
    | Concrete (_, (name, _), rhs, _) ->
        let v : var = find_var env (Unqualified name) in
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
let open_module_in (m: Module.name) (env: env): env =
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

let find_datacon env (datacon : Datacon.name maybe_qualified) : SurfaceSyntax.datacon_info * T.resolved_datacon =
  try
    let v, info = D.lookup_maybe_qualified datacon env.datacons in
    info, (tvar env v, unqualify datacon)
  with Not_found ->
    raise_error env (UnboundDataConstructor (unqualify datacon))

(* [locate env p] extends [env] with the provided location information. *)
let locate env p : env =
  { env with location = p }
;;

(* [extend env xs] extends the current environment with new bindings; [xs] is
   a fragment, that is, a map of identifiers to kinds. Because an arbitrary
   order is chosen for the bindings, the function returns not only an extended
   environment, but also a list of bindings, which indicates in which order
   the bindings are performed. At the head of the list comes the innermost
   binding. *)
let extend (env : env) (xs : type_binding list) : env =
  List.fold_left (fun env (x, k, _) ->
    bind env (x, k)) env xs
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
    (fun x -> bound_twice env x)

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

(* [names ty] returns a [fragment] containing all the names that [ty] binds. It
   is up to the [check] function to introduce the binders in scope in the right
   places. The order is not important here, since this will be passed on to the
   [extend] function which will then pick a give order. *)

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
    (fun x -> bound_twice env x);

  (* Return the bindings. *)
  bindings
;;

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
let rec check_fact_parameter (env: env) (x: Variable.name) (args: Variable.name list) (t: typ) =
  match t with
  | TyLocated (t, p) ->
      check_fact_parameter (locate env p) x args t
  | TyVar (Unqualified x') ->
      if not (List.exists (Variable.equal x') args) then
        bad_condition_in_fact env x
  | _ ->
      bad_condition_in_fact env x
;;


(* The conclusion of a fact, if any, must be the exact original type applied to
   the exact same arguments. *)
let rec check_fact_conclusion (env: env) (x: Variable.name) (args: Variable.name list) (t: typ) =
  match t with
  | TyLocated (t, p) ->
      check_fact_conclusion (locate env p) x args t
  | _ ->
      match flatten_tyapp t with
      | TyVar (Unqualified x'), args' ->
          Log.debug "%a %a" Variable.p x Variable.p x';
          if not (Variable.equal x x') then
            bad_conclusion_in_fact env x;
          if not (List.length args = List.length args') then
            bad_conclusion_in_fact env x;
          List.iter2 (fun x arg' ->
            match arg' with
            | TyVar (Unqualified x')
            | TyLocated (TyVar (Unqualified x'), _) ->
                if not (Variable.equal x x') then
                  bad_conclusion_in_fact env x;
            | _ ->
                bad_conclusion_in_fact env x) args args';
      | _ ->
          bad_conclusion_in_fact env x;
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

let rec check (env: env) (t: typ) (expected_kind: kind) =
  let inferred_kind = infer env t in
  if expected_kind <> inferred_kind then
    mismatch env expected_kind inferred_kind

and infer (env: env) (t: typ) =
  match t with
  | TyLocated (t, p) ->
      infer (locate env p) t

  | TyTuple ts ->
      List.iter (fun t -> check env t KType) ts;
      KType

  | TyUnknown
  | TyDynamic ->
      KType

  | TyEmpty ->
      KPerm

  | TyVar x ->
      find_kind env x

  | TyConcrete (branch, clause) ->
      (* TEMPORARY datacon is not checked here! *)
      check_branch env branch;
      Option.iter (fun t -> check env t KType) clause;
        (* If there is an [adopts] clause, we might wish to check that 
	   this data constructor is exclusive. We will do this in
	   [TransSurface]. *)
      KType

  | TySingleton t ->
      check env t KTerm;
      KType

  | TyApp (t1, t2s) ->
      let k1 = infer env t1 in
      let k2s, k = as_arrow k1 in
      let expected = List.length k2s
      and provided = List.length t2s in
      if expected <> provided then
	raise_error env (ArityMismatch (expected, provided));
      List.iter2 (check env) t2s k2s;
      k

  | TyArrow (t1, t2) ->
      let f1 = names env t1 in
      let f2 = names env t2 in
      let env = extend env f1 in
      check env t1 KType;
      let env = extend env f2 in
      check env t2 KType;
      KType

  | TyForall ((x, k, _), t)
  | TyExists ((x, k, _), t) ->
      let env = bind env (x, k) in
      infer_type_with_names env t

  | TyAnchoredPermission (t1, t2) ->
      check env t1 KTerm;
      check env t2 KType;
      KPerm

  | TyStar (t1, t2) ->
      check env t1 KPerm;
      check env t2 KPerm;
      KPerm

  | TyNameIntro (x, t) ->
      assert (find_kind env (Unqualified x) = KTerm);
      infer env t

  | TyConsumes t ->
      infer env t

  | TyBar (t1, t2) ->
      check env t1 KType;
      check env t2 KPerm;
      KType

  | TyAnd ((_, t), u)
  | TyImply ((_, t), u) ->
      check env t KType;
      infer env u

and check_field (env: env) (field: data_field_def) =
  match field with
  | FieldValue (_name, t) ->
      check_type_with_names env t KType
  | FieldPermission t ->
      (* I have removed the calls to [names] and [extend], because
	 a permission component does not bind any names. -fpottier *)
      check env t KPerm

and check_branch: 'a. env -> ('a * data_field_def list) -> unit = fun env branch ->
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

and check_type_with_names (env: env) (t: typ) (k: kind) =
  let bindings = names env t in
  let env = List.fold_left (fun env (x, k, _) -> bind env (x, k)) env bindings in
  check env t k

and infer_type_with_names (env: env) (t: typ): kind =
  let bindings = names env t in
  let env = List.fold_left (fun env (x, k, _) -> bind env (x, k)) env bindings in
  infer env t
;;


(* Check a data type definition. For abstract types, this just checks that the
   fact is well-formed. For concrete types, check that the branches are all
   well-formed. *)
let check_data_type_def (env: env) (def: data_type_def) =
  match def with
  | Abstract ((name, bindings), _return_kind, facts) ->
      (* Get the names of the parameters. *)
      let args = List.map (fun (_, (x, _, _)) -> x) bindings in
      (* Perform a tedious check. *)
      List.iter (function Fact (clauses, conclusion) ->
        List.iter (fun (_, t) -> check_fact_parameter env name args t) clauses;
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
          check_type_with_names env t KType;
          (* We can do that early. *)
	  if not (DataTypeFlavor.can_adopt flavor) then
	    raise_error env (AdopterNotExclusive name)
      end
  | Abbrev ((_, bindings), return_kind, t) ->
      let bindings = List.map (fun (_, (x, y, _)) -> x, y) bindings in
      let env = List.fold_left bind env bindings in
      check_type_with_names env t return_kind
;;


let check_data_type_group (env: env) (data_type_group: data_type_def list) =
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
    (duplicate_constructor env);

  (* Do the remainder of the checks. *)
  List.iter (check_data_type_def env) data_type_group
;;


let rec check_pattern (env: env) (pattern: pattern) =
  match pattern with
  | PConstraint (p, t) ->
      check_pattern env p;
      Log.debug "check_type_with_names";
      check_type_with_names env t KType
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


let rec check_patexpr (env: env) (flag: rec_flag) (pat_exprs: (pattern * expression) list): env =
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


and check_expression (env: env) (expr: expression) =
  match expr with
  | EConstraint (e, t) ->
      check_expression env e;
      check_type_with_names env t KType

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
      check_for_duplicate_variables Types.fst3 bindings (bound_twice env);
      let bindings = List.map (fun (x, y, _) -> x, y) bindings in
      let env = List.fold_left bind env bindings in
      let arg_bindings = names env arg in
      let env = extend env arg_bindings in
      check env arg KType;
      check_expression env body;
      let return_bindings = names env return_type in
      let env = extend env return_bindings in
      check env return_type KType

  | EAssign (e1, _, e2) ->
      check_expression env e1;
      check_expression env e2

  | EAssignTag (e1, _, _) ->
      check_expression env e1

  | EAccess (e, _) ->
      check_expression env e

  | EAssert t ->
      check env t KPerm

  | EApply (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | ETApply (e1, _) ->
      (* We are not checking the types here:
       * - we're calling [infer_type_with_names] in [typing/TransSurface.ml] to
       *   attach in the internal representation the kind of the type arguments;
       * - the [TypeChecker] will take care of checking that the kind of the
       *   arguments and the kind of the function variables match, once
       *   type-checking has been performed. *)
      check_expression env e1

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
;;


(* Because the binding structure of top-level declarations is possibly
 * complicated, because of patterns, this function does both the binding and the
 * checking at the same time (i.e. there's no [bindings_declaration_group]
 * function. However, it returns the environment with all the bindings added. *)
let check_declaration_group (env: env) = function
  | DLocated (DMultiple (rec_flag, pat_exprs), p) ->
    let env = locate env p in
    check_patexpr env rec_flag pat_exprs
  | _ ->
      Log.error "Unexpected shape for a [declaration_group]."
;;

let check_implementation (env: env) (program: implementation) : unit =
  let (_ : env) = List.fold_left (fun env -> function
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
        check_type_with_names env t KType;
        let env = bind env (x, KTerm) in
        env

    | OpenDirective mname ->
        open_module_in mname env
  ) env program in
  ()
;;

let check_interface (env: env) (interface: interface) =
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
  check_for_duplicate_variables fst all_bindings (bound_twice env);
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
  check_for_duplicate_datacons fst all_datacons (duplicate_constructor env);
    (* TEMPORARY this results in a dummy location *)

  (* Do all the regular checks. *)
  check_implementation env interface
;;

(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module KindPrinter = struct

  open MzPprint
  open TypeCore
  open Types
  open TypePrinter

  (* Prints an abstract data type. Very straightforward. *)
  let print_abstract_type_def print_env name kind =
    string "abstract" ^^ space ^^ print_var print_env name ^^ space ^^ colon ^^ space ^^
    print_kind kind
  ;;

  let print_variance = function
    | Invariant ->
        empty
    | Covariant ->
        plus
    | Contravariant ->
        minus
    | Bivariant ->
        equals
  ;;

  (* Prints a data type defined in the global scope. Assumes [print_env] has been
     properly populated. *)
  let print_data_type_def (env: env) name kind variance branches =
    let params, _return_kind = Kind.as_arrow kind in
    (* Turn the list of parameters into letters *)
    let letters: string list = name_gen (List.length params) in
    let letters = List.map2 (fun variance letter ->
      print_variance variance ^^ utf8string letter
    ) variance letters in
    let env, _, branches =
      bind_datacon_parameters env kind branches
    in
    let sep = break 1 ^^ bar ^^ space in
    (* The whole blurb *)
    string "data" ^^ space ^^ lparen ^^
    print_var env name ^^ space ^^ colon ^^ space ^^
    print_kind kind ^^ rparen ^^ concat_map (precede space) letters ^^
    space ^^ equals ^^
    jump
      (ifflat empty (bar ^^ space) ^^
      separate_map sep (print_unresolved_branch env) branches
      )
  ;;

  let print_abbrev_type_def (env: env) name kind variance t =
    let env, points = make_datacon_letters env kind false in
    let letters = List.map (fun p -> get_name env p) points in
    let letters = List.map2 (fun variance letter ->
      print_variance variance ^^ print_var env letter
    ) variance letters in
    let vars = List.map (fun x -> TyOpen x) points in
    let t = instantiate_type t vars in
    (* The whole blurb *)
    string "alias" ^^ space ^^ lparen ^^
    print_var env name ^^ space ^^ colon ^^ space ^^
    print_kind kind ^^ rparen ^^ concat_map (precede space) letters ^^
    space ^^ equals ^^ space ^^ print_type env t
  ;;

  let print_def env name kind variance def =
    match def with
    | Concrete branches ->
        print_data_type_def env name kind variance branches
    | Abbrev t ->
        print_abbrev_type_def env name kind variance t
    | Abstract ->
        print_abstract_type_def env name kind
  ;;

  (* This function prints the contents of a [Types.env]. *)
  let print_kinds env =
    (* Now we have a pretty-printing environment that's ready, proceed. *)
    let defs = fold_definitions env (fun acc var definition ->
      let name = get_name env var in
      let kind = get_kind env var in
      let variance = get_variance env var in
      print_def env name kind variance definition :: acc
    ) [] in
    separate (twice (break 1)) defs
  ;;

  let print_group env (group: data_type_group) =
    let defs = List.map (fun data_type ->
      let name = User (module_name env, data_type.data_name) in
      print_def env name data_type.data_kind data_type.data_variance data_type.data_definition
    ) group.group_items in
    nest 2 (separate (twice (break 1)) defs) ^^ hardline
  ;;


  let pgroup buf arg =
    pdoc buf ((fun (env, group) -> print_group env group), arg)
  ;;


  let print_kinds_and_facts program_env =
    colors.red ^^ string "KINDS:" ^^ colors.default ^^
    nest 2 (hardline ^^ print_kinds program_env) ^^ hardline ^^
    hardline ^^
    colors.red ^^ string "FACTS:" ^^ colors.default ^^
    nest 2 (hardline ^^ print_facts program_env) ^^ hardline
  ;;

end
