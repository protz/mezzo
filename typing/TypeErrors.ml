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

(** Unified error handling *)

open TypeCore
open Types
open Expressions

type error = env * raw_error

and raw_error =
  | CyclicDependency of Module.name
  | NotAFunction of var
  | HasFlexible of typ
  | ExpectedType of typ * var
  | RecursiveOnlyForFunctions
  | MissingField of Field.name
  | ExtraField of Field.name
  | NoSuchField of var * Field.name
  | FieldMismatch of typ * Datacon.name
  | CantAssignTag of var
  | NoSuchFieldInPattern of pattern * Field.name
  | BadPattern of pattern * var
  | BadField of Datacon.name * Field.name
  | SubPattern of pattern
  | NoTwoConstructors of var
  | MatchBadDatacon of var * Datacon.name
  | MatchBadTuple of var
  | NoSuchPermission of typ
  | AssignNotExclusive of typ * Datacon.name
  | FieldCountMismatch of typ * Datacon.name
  | NoMultipleArguments
  | ResourceAllocationConflict of var
  | UncertainMerge of var
  | ConflictingTypeAnnotations of typ * typ
  | IllKindedTypeApplication of tapp * kind * kind
  | BadTypeApplication of var
  | PolymorphicFunctionCall
  | BadFactForAdoptedType of var * typ * fact
  | NoAdoptsClause of var
  | NotDynamic of var
  | NoSuitableTypeForAdopts of var * typ
  | AdoptsNoAnnotation
  | NotMergingClauses of env * typ * typ * env * typ * typ
  | MissingFieldInSignature of Variable.name
  | NoSuchTypeInSignature of var * typ
  | DataTypeMismatchInSignature of Variable.name * string
  | NotExclusiveOwns of var
  | UnsatisfiableConstraint of duplicity_constraint list
  | VarianceAnnotationMismatch

exception TypeCheckerError of error

let raise_error env e =
  raise (TypeCheckerError (env, e))
;;

(* -------------------------------------------------------------------------- *)

(* For pretty-printing. *)

exception NotFoldable

(** [fold_var env var] tries to find (hopefully) one "main" type for [var], by
    folding back its "main" type [t] into a form that's suitable for one
    thing, and one thing only: printing. *)
let rec fold_var (env: env) (var: var): (env * typ) option =
  if is_flexible env var then raise NotFoldable;

  let perms = get_permissions env var in
  let perms = List.filter
    (function
      | TySingleton (TyOpen p) when same env p var ->
          false
      | TyUnknown ->
          false
      | _ ->
          true
    ) perms
  in
  match perms with
  | [] ->
      Some (env, TyUnknown)
  | t :: []
  | TyDynamic :: t :: []
  | t :: TyDynamic :: [] ->
      begin try
        let env, t = fold_type_raw env t in
        let env = set_permissions env var [TyDynamic] in
        Some (env, t)
      with NotFoldable ->
        None
      end
  | _ ->
      None


and fold_type_raw (env: env) (t: typ): env * typ =
  match t with
  | TyUnknown
  | TyDynamic ->
      env, t

  | TyBound _ ->
      Log.error "All types should've been opened at that stage"

  | TyOpen _ ->
      env, t

  | TyForall _
  | TyExists _
  | TyApp _ ->
      env, t

  | TySingleton (TyOpen p) ->
      begin match fold_var env p with
      | Some t ->
          t
      | None ->
          raise NotFoldable
      end

  | TyTuple components ->
      let env, components =
        List.fold_left (fun (env, cs) t ->
          let env, t = fold_type_raw env t in
          env, t :: cs
        ) (env, []) components
      in
      let components = List.rev components in
      env, TyTuple components

  | TyImply (cs, t) ->
      let env, t = fold_type_raw env t in
      env, TyImply (cs, t)

  | TyAnd (cs, t) ->
      let env, t = fold_type_raw env t in
      env, TyAnd (cs, t)

  | TyConcreteUnfolded (dc, fields, clause) ->
      let env, fields = List.fold_left (fun (env, fields) -> function
        | FieldPermission p ->
            let env, p = fold_type_raw env p in
            env, FieldPermission p :: fields
        | FieldValue (n, t) ->
            let env, t = fold_type_raw env t in
            env, FieldValue (n, t) :: fields
      ) (env, []) fields in
      let fields = List.rev fields in
      let env, clause = fold_type_raw env clause in
      env, TyConcreteUnfolded (dc, fields, clause)

  | TySingleton _ ->
      env, t

  | TyArrow _ ->
      env, t

  | TyBar (t, p) ->
      let env, t = fold_type_raw env t in
      env, TyBar (t, p)

  | TyAnchoredPermission (x, t) ->
      let env, t = fold_type_raw env t in
      env, TyAnchoredPermission (x, t)

  | TyEmpty ->
      env, t

  | TyStar _ ->
      Log.error "Huh I don't think we should have that here"

;;

let fold_type env t =
  try
    let _, t = fold_type_raw env t in
    Some t
  with NotFoldable ->
    None
;;

let fold_var env t =
  Option.map snd (fold_var env t)
;;

(* -------------------------------------------------------------------------- *)

(* The main error printing function. *)

let print_error buf (env, raw_error) =
  let open TypePrinter in
  let open ExprPrinter in
  let print_permissions () =
    Printf.bprintf buf "\nOH NOES. Printing permissions.\n\n%a" pdoc (print_permissions, env);
    Printf.bprintf buf "\nError message follows.\n\n";
  in
  if Log.debug_level () >= 5 then
    print_permissions ();
  match raw_error with
  | NotAFunction p ->
      begin match fold_var env p with
      | Some t ->
          Printf.bprintf buf
            "%a %a is not a function, it has type:\n%a"
            Lexer.p (location env)
            pname (env, p)
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a is not a function, the only permissions available for it are:\n%a"
            Lexer.p (location env)
            pname (env, p)
            ppermission_list (env, p)
      end
  | NoSuchPermission t ->
      Printf.bprintf buf
        "%a unable to extract the following permission:\n%a"
        Lexer.p (location env)
        ptype (env, t);
  | HasFlexible t ->
      Printf.bprintf buf
        "%a the following type still contains flexible variables:\n%a"
        Lexer.p (location env)
        ptype (env, t);
  | ExpectedType (t, var) ->
      let t1 = fold_type env t in
      let t2 = fold_var env var in
      begin match t1, t2 with
      | Some t1, Some t2 -> (* #winning *)
          Printf.bprintf buf
            "%a expected an expression of type:\n%a\nbut this expression has type:\n%a\n"
            Lexer.p (location env)
            ptype (env, t1)
            ptype (env, t2)
      | _ ->
          Printf.bprintf buf
            "%a expected an argument of type:\n%a but the only permissions available for %a are:\n%a"
            Lexer.p (location env)
            ptype (env, t) pname (env, var)
            ppermission_list (env, var)
      end
  | RecursiveOnlyForFunctions ->
      Printf.bprintf buf
        "%a recursive definitions are enabled for functions only"
        Lexer.p (location env)
  | MissingField f ->
      Printf.bprintf buf
        "%a field %a is missing in that constructor"
        Lexer.p (location env)
        Field.p f
  | ExtraField f ->
      Printf.bprintf buf
        "%a field %a is superfluous in that constructor"
        Lexer.p (location env)
        Field.p f
  | NoTwoConstructors var ->
      begin match fold_var env var with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type:\n%a\nIt is not a type with two constructors"
            Lexer.p (location env)
            pname (env, var)
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission for a type with two constructors;\n\
              the only permissions available for it are:\n%a"
            Lexer.p (location env)
            pname (env, var)
            ppermission_list (env, var)
      end
  | NoSuchField (var, f) ->
      begin match fold_var env var with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type:\n%a\nThere is no field named %a"
            Lexer.p (location env)
            pname (env, var)
            ptype (env, t)
            Field.p f
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission with field %a;\n\
             the only permissions available for it are:\n%a"
            Lexer.p (location env)
            pname (env, var)
            Field.p f
            ppermission_list (env, var)
      end
  | FieldMismatch (t, datacon) ->
      Printf.bprintf buf
        "%a user-provided type:\n%a\ndoes not match the fields of data constructor %a"
        Lexer.p (location env)
        ptype (env, t)
        Datacon.p datacon
  | CantAssignTag var ->
      begin match fold_var env var with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type:\n%a\nWe can't assign a tag to it"
            Lexer.p (location env)
            pname (env, var)
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission that would accept a tag update, \
              the only permissions available for it are:\n%a"
            Lexer.p (location env)
            pname (env, var)
            ppermission_list (env, var)
      end
  | SubPattern pat ->
      Printf.bprintf buf
        "%a there's a sub-constraint in that pattern, not allowed: %a"
        Lexer.p (location env)
        ppat (env, pat)
  | MatchBadTuple p ->
      Printf.bprintf buf
        "%a trying to match a tuple against a var whose only \
          permissions are:\n%a"
        Lexer.p (location env)
        ppermission_list (env, p)
  | MatchBadDatacon (p, datacon) ->
      Printf.bprintf buf
        "%a trying to match data constructor %a against a var whose only \
          permissions are:\n%a"
        Lexer.p (location env)
        Datacon.p datacon
        ppermission_list (env, p)
  | NoSuchFieldInPattern (pat, field) ->
      Printf.bprintf buf
        "%a the pattern %a mentions field %a which is unknown for that branch"
        Lexer.p (location env)
        ppat (env, pat)
        Field.p field
  | BadPattern (pat, var) ->
      Printf.bprintf buf
        "%a cannot match pattern %a against %a, the only permissions available for it are:\n%a"
        Lexer.p (location env)
        ppat (env, pat)
        pname (env, var)
        ppermission_list (env, var)
  | BadField (datacon, name) ->
      Printf.bprintf buf "%a this pattern mentions field %a but data constructor \
          %a has no such field"
        Lexer.p (location env)
        Field.p name
        Datacon.p datacon

  | AssignNotExclusive (t, datacon) ->
      Printf.bprintf buf
        "%a this value has type %a: constructor %a belongs to a data type that \
          is not defined as exclusive"
        Lexer.p (location env)
        ptype (env, t)
        Datacon.p datacon
  | FieldCountMismatch (t, datacon) ->
      Printf.bprintf buf
        "%a this value has type %a: constructor %a belongs to a data type that \
          does not have the same number of fields"
        Lexer.p (location env)
        ptype (env, t)
        Datacon.p datacon
  | NoMultipleArguments ->
      Printf.bprintf buf
        "%a functions take only one tuple argument in HaMLet"
        Lexer.p (location env)
  | ResourceAllocationConflict var ->
      Printf.bprintf buf "%a exclusive resource allocation conflict on %a"
        Lexer.p (location env)
        pnames (env, get_names env var);
  | UncertainMerge var ->
      Printf.bprintf buf "%a merging distinct constructors into a nominal \
          type with type parameters, results are unpredictable, you should \
          consider providing annotations for %a"
        Lexer.p (location env)
        pnames (env, get_names env var)
  | ConflictingTypeAnnotations (t1, t2) ->
      Printf.bprintf buf "%a the context provides a type annotation, namely %a \
        but here is a type annotation, namely %a, that is conflicting the \
        context-provided type annotation"
        Lexer.p (location env)
        ptype (env, t1)
        ptype (env, t2);
  | BadTypeApplication var ->
      Printf.bprintf buf "%a var %a does not have a polymorphic type, the only \
          permissions available for it are %a"
        Lexer.p (location env)
        pnames (env, get_names env var)
        ppermission_list (env, var)
  | IllKindedTypeApplication (t, k, k') ->
      Printf.bprintf buf "%a while applying type %a: this type has kind %a but \
          the sub-expression has a polymorphic type with kind %a"
        Lexer.p (location env)
        pdoc ((fun t -> ExprPrinter.print_tapp env t), t)
        pdoc (print_kind, k) 
        pdoc (print_kind, k');
  | PolymorphicFunctionCall ->
      Printf.bprintf buf "%a this is a polymorphic function call, results are \
          undefined; consider using a type application"
        Lexer.p (location env)
  | BadFactForAdoptedType (p, t, f) ->
      Printf.bprintf buf "%a type %a cannot adopt type %a because it is not \
          marked as exclusive but %a"
        Lexer.p (location env)
        pnames (env, get_names env p)
        ptype (env, t)
        pfact f
  | NoAdoptsClause p ->
      Printf.bprintf buf "%a trying to give/take to/from %a but this expression \
          cannot adopt; the only permissions available for it are %a"
        Lexer.p (location env)
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | NotDynamic p ->
      Printf.bprintf buf "%a cannot take %a as it is not dynamic, the only \
          permissions available for it are %a"
        Lexer.p (location env)
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | NoSuitableTypeForAdopts (p, t) ->
      Printf.bprintf buf "%a trying to give/take %a to/from some expression, but \
          the expression adopts %a and the only permissions available for %a are %a"
        Lexer.p (location env)
        pnames (env, get_names env p)
        ptype (env, t)
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | AdoptsNoAnnotation ->
      Printf.bprintf buf "%a in this “give e1 to e2” statement, please provide a \
          type annotation for e1"
        Lexer.p (location env);
  | NotMergingClauses (left_env, left_var, left_t, right_env, right_var, right_t) ->
      Printf.bprintf buf "%a while merging %a and %a, it turns out they have \
          different adopts clauses, namely %a and %a; I refuse to merge these, \
          so please annotate using identical adopts clauses"
        Lexer.p (location env)
        ptype (left_env, left_var)
        ptype (right_env, right_var)
        ptype (left_env, left_t)
        ptype (right_env, right_t)
  | MissingFieldInSignature name ->
      Printf.bprintf buf "%a this file does not export a variable named %a"
        Lexer.p (location env)
        Variable.p name
  | NoSuchTypeInSignature (p, t) ->
      Printf.bprintf buf "%a this file exports a variable named %a, but it does \
        not have type %a, the only permissions available for it are: %a"
        Lexer.p (location env)
        pname (env, p)
        ptype (env, t)
        ppermission_list (env, p)
  | DataTypeMismatchInSignature (x, reason) ->
      Printf.bprintf buf "%a cannot match the definition of %a against the \
          signature because of: %s"
        Lexer.p (location env)
        Variable.p x
        reason
  | NotExclusiveOwns p ->
      Printf.bprintf buf "%a %a is not exclusive so it canno hold anything; \
          the only permissions available for it are %a"
        Lexer.p (location env)
        pname (env, p)
        ppermission_list (env, p)
  | CyclicDependency m ->
      Printf.bprintf buf "There is a cyclic dependency on module %a" Module.p m
  | UnsatisfiableConstraint cs ->
      Printf.bprintf buf "%a one of the following constraints cannot be satisfied: %a"
        Lexer.p (location env)
        pconstraints (env, cs)
  | VarianceAnnotationMismatch ->
      Printf.bprintf buf "%a the variance annotations do not match the inferred ones"
        Lexer.p (location env)
;;

let html_error error =
  let env = fst error in
  (* Get a plain-text version of the error *)
  MzPprint.disable_colors ();
  let text = MzString.bsprintf "%a\n" print_error error in
  (* Generate the HTML explanation. *)
  Debug.explain ~text env;
  (* Find out about the command to run. *)
  let f = (fst (TypeCore.location env)).Lexing.pos_fname in
  let f = MzString.replace "/" "_" f in
  let cmd = Printf.sprintf
    "firefox -new-window \"viewer/viewer.html?json_file=data/%s.json\" &"
    f
  in
  (* Let's do it! *)
  ignore (Sys.command cmd)
;;

let warn_or_error env error =
  (* FIXME switch to a better error system *)
  if !Options.pedantic then
    Log.warn "%a" print_error (env, error)
  else if false then
    raise_error env error
;;

let internal_extracterror = snd;;
