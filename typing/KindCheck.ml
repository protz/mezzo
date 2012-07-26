(* This module implements a well-kindedness check for the types of
   the surface language. [Note Jonathan: a clean version of the rules can be
   found in my thesis noteboook, date June, 16th 2012]. *)

open SurfaceSyntax
module T = Types
module E = Expressions


(* ---------------------------------------------------------------------------- *)

(* Maps of identifiers to things. *)

module M =
  Variable.Map

(* An environment maps an identifier to a pair of a kind and a de Bruijn level
   (not to be confused with a de Bruijn index!). An environment also keeps
   track of the current de Bruijn level.
   
   This binding representation is specific to this first phase -- we use more
   sophisticated environments later on, and the level thing is just some sort of
   hack. *)

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


(* ---------------------------------------------------------------------------- *)

(* Error messages. *)

type error = env * raw_error

and raw_error =
  | Unbound of Variable.name
  | Mismatch of kind * kind
  | NotAnArrow of kind
  | BoundTwice of Variable.name
  | IllegalConsumes
  | BadConditionsInFact of Variable.name
  | BadConclusionInFact of Variable.name
  | DuplicateConstructor of Variable.name * Datacon.name

exception KindError of error

let raise_error env e =
  raise (KindError (env, e))
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
  | NotAnArrow (kind) ->
      Printf.bprintf buf
        "%a cannot apply arguments to this type since it has kind %a"
        Lexer.p env.location
        p_kind kind
  | BoundTwice x ->
      Printf.bprintf buf
        "%a variable %a is bound twice"
        Lexer.p env.location
        Variable.p x
  | IllegalConsumes ->
      Printf.bprintf buf
        "%a unexpected consumes annotation"
        Lexer.p env.location
  | BadConditionsInFact x ->
      Printf.bprintf buf
        "%a the conditions for the fact about %a can only be type variables"
        Lexer.p env.location
        Variable.p x
  | BadConclusionInFact x ->
      Printf.bprintf buf
        "%a the conclusion for the fact about %a can only be %a applied to its \
        parameters"
        Lexer.p env.location
        Variable.p x
        Variable.p x
  | DuplicateConstructor (x, d) ->
      Printf.bprintf buf
        "%a type %a defines constructor %a several times"
        Lexer.p env.location
        Variable.p x
        Datacon.p d
  end;
  (* Uncomment this part to get a really verbose error message. *)
  Printf.bprintf buf "\n";
  let bindings = M.fold (fun x (kind, level) acc ->
    (level, (x, kind)) :: acc) env.mapping []
  in
  let bindings = List.sort (fun (x, _) (y, _) -> compare x y) bindings in
  List.iter (fun (level, (x, kind)) ->
    Printf.bprintf buf "  [debug] level=%d, variable=%a, kind=%a\n"
      level
      Variable.p x
      p_kind kind
  ) bindings;
;;

let unbound env x =
  raise_error env (Unbound x)

let mismatch env expected_kind inferred_kind =
  raise_error env (Mismatch (expected_kind, inferred_kind))

let illegal_consumes env =
  raise_error env IllegalConsumes

let bound_twice env x =
  raise_error env (BoundTwice x)

let bad_condition_in_fact env x =
  raise_error env (BadConditionsInFact x)

let bad_conclusion_in_fact env x =
  raise_error env (BadConclusionInFact x)

let duplicate_constructor env x d =
  raise_error env (DuplicateConstructor (x, d))


(* ---------------------------------------------------------------------------- *)

(* Kind constructors. *)

let karrow bindings kind =
  List.fold_right (fun (_, kind1) kind2 ->
    KArrow (kind1, kind2)
  ) bindings kind

let deconstruct_arrow env = function
  | KArrow (k1, k2) ->
      k1, k2
  | kind ->
      raise_error env (NotAnArrow kind)


(* ---------------------------------------------------------------------------- *)

(* Working with environments *)

type fragment =
    kind M.t

(* [strict_add x kind env] adds the name [x] in the environment [env] with kind
   [kind], and ensures that is hasn't been bound already. *)
let strict_add env x kind mapping =
  try
    M.strict_add x kind mapping
  with M.Unchanged ->
    bound_twice env x

(* [find x env] looks up the name [x] in the environment [env] and returns a
   pair of a kind and a de Bruijn index (not a de Bruijn level!). *)
let find x env =
  try
    let kind, level = M.find x env.mapping in
    kind, env.level - level - 1
  with Not_found ->
    unbound env x

(* [bind env (x, kind)] binds the name [x] with kind [kind]. *)
let bind ?strict env (x, kind) : env =
  (* The current level becomes [x]'s level. The current level is
     then incremented. *)
  let add = if Option.unit_bool strict then strict_add env else M.add in
  { env with
    level = env.level + 1;
    mapping = add x (kind, env.level) env.mapping }

(* [locate env p1 p2] extends [env] with the provided location information. *)
let locate env p1 p2: env =
  { env with location = p1, p2 }

(* [extend env xs] extends the current environment with new bindings; [xs] is
   a fragment, that is, a map of identifiers to kinds. Because an arbitrary
   order is chosen for the bindings, the function returns not only an extended
   environment, but also a list of bindings, which indicates in which order
   the bindings are performed. At the head of the list comes the innermost
   binding. *)
let extend (env : env) (xs : type_binding list) : env =
  List.fold_left (fun env (x, k, _) ->
    bind env (x, k)) env xs

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

(* Some helper functions for working with [SurfaceSyntax] types. *)

let flatten_tyapp t =
  let rec flatten_tyapp acc = function
    | TyApp (t1, t2) ->
        flatten_tyapp (t2 :: acc) t1
    | _ as x ->
        x, acc
  in
  flatten_tyapp [] t
;;

let check_for_duplicates (elements: 'a list) (exit: 'a -> 'b): unit =
  let tbl = Hashtbl.create 11 in
  List.iter (fun x ->
    if Hashtbl.mem tbl x then
      exit x
    else
      Hashtbl.add tbl x ()) elements
;;


(* ---------------------------------------------------------------------------- *)

(* The ↑ relation, which we implement as [names]. *)

(* [names ty] returns a [fragment] containing all the names that [ty] binds. It
   is up to the [check] function to introduce the binders in scope in the right
   places. The order is not important here, since this will be passed on to the
   [extend] function which will then pick a give order. *)
let names env ty : type_binding list =
  let rec names env ty =
    match ty with
    | TyLocated (t, p1, p2) ->
        names (locate env p1 p2) t
    | TyNameIntro (x, t) ->
        let bindings = names env t in
        (x, KTerm, env.location) :: bindings
    | TyTuple ts ->
        List.flatten (List.map (names env) ts)
    | TyConcreteUnfolded (_cons, fields) ->
        let ts = Hml_List.map_some
          (function FieldValue (_, t) -> Some t | FieldPermission _ -> None) 
          fields
        in
        List.flatten (List.map (names env) ts)
    | TySingleton t
    | TyConsumes t
    | TyForall (_, t) ->
        names env t
    | TyStar (t1, t2)
    | TyAnchoredPermission (t1, t2)
    | TyBar (t1, t2) ->
        (names env t1) @ (names env t2)
    | TyUnknown | TyDynamic | TyEmpty | TyVar _ | TyApp _ | TyArrow _ ->
        []
  in
  let names = names env ty in
  check_for_duplicates
    (List.map (fun (x, _, _) -> x) names)
    (fun x -> bound_twice env x);
  names
;;

(* [bindings_data_type_group] returns a list of names that the whole data type
   group binds, with the corresponding kinds. The list is in the same order as
   the data type definitions. *)
let bindings_data_type_group (data_type_group: data_type_def list): (Variable.name * kind) list =
  List.map (function
      | Concrete (_flag, (name, params), _) ->
          let params = List.map (fun (x, y, _) -> x, y) params in
          let k = karrow params KType in
          (name, k)
      | Abstract ((name, params), return_kind, _fact) ->
          let params = List.map (fun (x, y, _) -> x, y) params in
          let k = karrow params return_kind in
          (name, k))
    data_type_group
;;


(* [bindings_pattern] returns in prefix order the list of names bound in a
   pattern. *)
let rec bindings_pattern (pattern: pattern): (Variable.name * kind) list =
  match pattern with
  | PConstraint (p, _) ->
      bindings_pattern p
  | PVar x ->
      [x, KTerm]
  | PTuple patterns ->
      List.flatten (List.map bindings_pattern patterns)
  | PConstruct (_, name_pats) ->
      let _, patterns = List.split name_pats in
      List.flatten (List.map bindings_pattern patterns)
  | PLocated (p, _, _) ->
      bindings_pattern p
;;



(* ---------------------------------------------------------------------------- *)

(* The kind-checking functions. *)


(* This just makes sure that the type parameters mentioned in the fact are in
   the list of the original type parameters. *)
let rec check_fact_parameter (env: env) (x: Variable.name) (args: Variable.name list) (t: typ) =
  match t with
  | TyLocated (t, p1, p2) ->
      check_fact_parameter (locate env p1 p2) x args t
  | TyVar x' ->
      if not (List.exists (Variable.equal x') args) then
        bad_condition_in_fact env x
  | _ ->
      bad_condition_in_fact env x
;;


(* The conclusion of a fact, if any, must be the exact original type applied to
   the exact same arguments.
   
   TEMPORARY: this function implements a purely syntactic check, which only
   allows for a very limited form of facts. We should recognize both in the
   parser and here a more general form of facts, with a conjunction of
   hypotheses that entail an arbitrary predicate. *)
let rec check_fact_conclusion (env: env) (x: Variable.name) (args: Variable.name list) (t: typ) =
  match t with
  | TyLocated (t, p1, p2) ->
      check_fact_conclusion (locate env p1 p2) x args t
  | _ ->
      match flatten_tyapp t with
      | TyVar x', args' ->
          if not (Variable.equal x x') then
            bad_conclusion_in_fact env x;
          if not (List.length args = List.length args') then
            bad_conclusion_in_fact env x;
          List.iter2 (fun x arg' ->
            match arg' with
            | TyVar x' when Variable.equal x x' ->
                ()
            | _ ->
                bad_conclusion_in_fact env x) args args';
      | _ ->
          bad_conclusion_in_fact env x;
;;


let rec check (env: env) (t: typ) (expected_kind: kind) =
  let inferred_kind = infer env t in
  if expected_kind <> inferred_kind then
    mismatch env expected_kind inferred_kind

and infer (env: env) (t: typ) =
  match t with
  | TyLocated (t, p1, p2) ->
      infer (locate env p1 p2) t

  | TyTuple ts ->
      List.iter (fun t -> check env t KType) ts;
      KType

  | TyUnknown
  | TyDynamic ->
      KType

  | TyEmpty ->
      KPerm

  | TyVar x ->
      let kind, _index = find x env in
      kind

  | TyConcreteUnfolded branch ->
      check_data_type_def_branch env branch;
      KType

  | TySingleton t ->
      check env t KTerm;
      KType

  | TyApp (t1, t2) ->
      let k, k' = deconstruct_arrow env (infer env t1) in
      check env t2 k;
      k'

  | TyArrow (t1, t2) ->
      let f1 = names env t1 in
      let f2 = names env t2 in
      let env = extend env f1 in
      check env t1 KType;
      let env = extend env f2 in
      check env t2 KType;
      KType

  | TyForall ((x, k, _), t) ->
      let env = bind env (x, k) in
      infer env t

  | TyAnchoredPermission (t1, t2) ->
      check env t1 KTerm;
      check env t2 KType;
      KPerm

  | TyStar (t1, t2) ->
      check env t1 KPerm;
      check env t2 KPerm;
      KPerm

  | TyNameIntro (x, t) ->
      ignore (find x env);
      infer env t

  | TyConsumes t ->
      infer env t

  | TyBar (t1, t2) ->
      check env t1 KType;
      check env t2 KPerm;
      KType

and check_field (env: env) (field: data_field_def) =
  match field with
  | FieldValue (_name, t) ->
      let fragment = names env t in
      let env = extend env fragment in
      check env t KType
  | FieldPermission t ->
      let fragment = names env t in
      let env = extend env fragment in
      check env t KPerm

and check_data_type_def_branch (env: env) (branch: data_type_def_branch) =
  let _datacon, fields = branch in
  List.iter (check_field env) fields
;;


(* Check a data type definition. For abstract types, this just checks that the
   fact is well-formed. For concrete types, check that the branches are all
   well-formed. *)
let check_data_type_def (env: env) (def: data_type_def) =
  match def with
  | Abstract ((name, bindings), _return_kind, fact) ->
      (* Get the names of the parameters. *)
      let args = List.map (fun (x, _, _) -> x) bindings in
      (* Perform a tedious check. *)
      begin match fact with
      | Some (FDuplicableIf (clauses, conclusion)) ->
          List.iter (check_fact_parameter env name args) clauses;
          check_fact_conclusion env name args conclusion
      | Some (FExclusive conclusion) ->
          check_fact_conclusion env name args conclusion
      | None ->
          ()
      end
  | Concrete (_flag, (name, bindings), branches) ->
      let bindings = List.map (fun (x, y, _) -> x, y) bindings in
      let env = List.fold_left bind env bindings in
      (* Check that the constructors are unique. *)
      let constructors = fst (List.split branches) in
      check_for_duplicates constructors (fun x -> duplicate_constructor env name x);
      (* Check the branches. *)
      List.iter (check_data_type_def_branch env) branches
;;


let check_data_type_group (env: env) (data_type_group: data_type_def list) =
  List.iter (check_data_type_def env) data_type_group
;;


let rec check_pattern (env: env) (pattern: pattern) =
  match pattern with
  | PConstraint (p, t) ->
      check_pattern env p;
      check env t KType
  | PVar x ->
      ignore (find x env)
  | PTuple patterns ->
      List.iter (check_pattern env) patterns
  | PConstruct (_, name_pats) ->
      let _, patterns = List.split name_pats in
      List.iter (check_pattern env) patterns
  | PLocated (p, _, _) ->
      check_pattern env p
;;


let rec check_patexpr (env: env) (flag: rec_flag) (pat_exprs: (pattern * expression) list): env =
  let patterns, expressions = List.split pat_exprs in
  (* Introduce all bindings from the patterns *)
  let bindings = List.flatten (List.map bindings_pattern patterns) in
  check_for_duplicates
    (fst (List.split bindings))
    (fun x -> bound_twice env x);
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
      check env t KType

  | EVar x ->
      let k, _ = find x env in
      if k <> KTerm then
        mismatch env KTerm k
      
  | ELet (flag, pat_exprs, expr) ->
      let env = check_patexpr env flag pat_exprs in
      check_expression env expr

  | EFun (bindings, arg, return_type, body) ->
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

  | EAccess (e, _) ->
      check_expression env e

  | EAssert t ->
      check env t KPerm

  | EApply (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | EMatch (_, e, pat_exprs) ->
      check_expression env e;
      List.iter (fun (pat, expr) ->
        let bindings = bindings_pattern pat in
        check_for_duplicates bindings (fun (x, _) -> bound_twice env x);
        let sub_env = List.fold_left bind env bindings in
        check_pattern sub_env pat;
        check_expression sub_env expr
      ) pat_exprs

  | ETuple exprs ->
      List.iter (check_expression env) exprs

  | EConstruct (_, field_exprs) ->
      let _, exprs = List.split field_exprs in
      List.iter (check_expression env) exprs

  | EIfThenElse (_, e1, e2, e3) ->
      check_expression env e1;
      check_expression env e2;
      check_expression env e3

  | ESequence (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | ELocated (e, p1, p2) ->
      check_expression (locate env p1 p2) e

  | EPlus (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | EMinus (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | ETimes (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | EDiv (e1, e2) ->
      check_expression env e1;
      check_expression env e2

  | EUMinus e ->
      check_expression env e

  | EInt _ ->
      ()

  | EExplained e ->
      check_expression env e
;;


let check_declaration_group (env: env) (declaration_group: declaration list) =
  let rec check_declaration_group env decls =
    match decls with
    | DLocated (DMultiple (rec_flag, pat_exprs), p1, p2) :: decls ->
      let env = locate env p1 p2 in
      let env = check_patexpr env rec_flag pat_exprs in
      check_declaration_group env decls
    | [] ->
        ()
    | _ ->
        Log.error "Unexpected shape for a [declaration_group]."
  in
  check_declaration_group env declaration_group
;;

let check_program (program: program) =
  (* A program is made up of a data type definitions and value definitions. We
   * will probably want to change that later on, this should be easily doable in
   * this function. *)
  let data_type_group, declaration_group = program in
  (* First collect the names from the data type definitions, since they will be
   * made available in both the data type definitions themselves, and the value
   * definitions. All definitions in a data type groupe are mutually recursive. *)
  let bindings = bindings_data_type_group data_type_group in
  (* Create an environment that already features those names. *)
  let env = List.fold_left (bind ~strict:()) empty bindings in 
  (* Check both the data type definitions and the values in the freshly-created
   * environment. *)
  check_data_type_group env data_type_group;
  check_declaration_group env declaration_group;
;;

(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module KindPrinter = struct

  open Hml_Pprint
  open Types
  open TypePrinter

  (* Prints an abstract data type. Very straightforward. *)
  let print_abstract_type_def _print_env name kind =
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
    let env, _, branches = bind_datacon_parameters env kind branches in
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
    let defs = map_types env (fun { names; kind; _ } { definition; _ } ->
      let name = List.hd names in
      match definition with
      | Some (Some (flag, branches), _) ->
          print_data_type_def env flag name kind branches
      | Some (None, _) ->
          print_abstract_type_def env name kind
      | None ->
          Log.error "This is strange"
    ) in
    join (break1 ^^ break1) defs
  ;;

  let print_kinds_and_facts program_env =
    colors.red ^^ string "KINDS:" ^^ colors.default ^^
    nest 2 (hardline ^^ print_kinds program_env) ^^ hardline ^^
    hardline ^^
    colors.red ^^ string "FACTS:" ^^ colors.default ^^
    nest 2 (hardline ^^ print_facts program_env) ^^ hardline
  ;;

end

