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

open Kind
open TypeCore
open Types
open DerivationPrinter
open ClFlags
open ExpressionsCore
open ResugarFold

type error = env * raw_error

and raw_error =
  | CyclicDependency of Module.name
  | NotAFunction of var
  | ExpectedType of typ * var * Derivations.derivation
  | ExpectedPermission of typ * Derivations.derivation
  | RecursiveOnlyForFunctions
  | MissingField of Field.name
  | ExtraField of Field.name
  | NoSuchField of var * Field.name
  | CantAssignTag of var
  | NoSuchFieldInPattern of pattern * Field.name
  | BadPattern of pattern * var
  | BadField of Datacon.name * Field.name
  | NoTwoConstructors of var
  | MatchBadDatacon of var * Datacon.name
  | MatchBadTuple of var
  | AssignNotExclusive of typ * Datacon.name
  | FieldCountMismatch of typ * Datacon.name
  | NoMultipleArguments
  | ResourceAllocationConflict of var
  | UncertainMerge of var
  | ConflictingTypeAnnotations of typ * typ
  | IllKindedTypeApplication of tapp * kind * kind
  | BadTypeApplication of var
  | NonExclusiveAdoptee of typ
  | NoAdoptsClause of var
  | NotDynamic of var
  | NoSuitableTypeForAdopts of var * typ
  | AdoptsNoAnnotation
  | NotMergingClauses of env * typ * typ * env * typ * typ
  | NoSuchTypeInSignature of var * typ * Derivations.derivation
  | DataTypeMismatchInSignature of Variable.name * string
  | VarianceAnnotationMismatch
  | ExportNotDuplicable of Variable.name
  | LocalType
  | Instantiated of Variable.name * typ
  | PackWithExists
  | SeveralWorkingFunctionTypes of var

exception TypeCheckerError of error

let raise_error env e =
  raise (TypeCheckerError (env, e))
;;

(* -------------------------------------------------------------------------- *)

(* The main error printing function. *)

open TypePrinter

let print_error buf (env, raw_error) =
  let bprintf s = Printf.bprintf buf s in
  (* Extra verbose debugging output. *)
  if Log.debug_level () >= 5 then begin
    bprintf "\nOH NOES. Printing permissions.\n\n%a" MzPprint.pdoc (print_permissions, env);
    bprintf "\nError message follows.\n\n";
  end;
  (* A few error messages are printed *without* an error location. *)
  begin match raw_error with
    | CyclicDependency _ ->
        ()
    | _ ->
      Lexer.p buf (location env)    
  end;
  (* Now, print an error-specific message. *)
  match raw_error with
  | CyclicDependency m ->
      (* TEMPORARY cyclic dependencies are hard to understand, so
        showing the cycle in a more explicit manner would be useful *)
      bprintf "There is a cyclic dependency on module %a" Module.p m
  | NotAFunction p ->
      begin match fold_var env p with
      | Some t ->
          bprintf
            "%a is not a function, it has type:\n%a"
            pname (env, p)
            ptype (env, t)
      | None ->
          bprintf
            "%a is not a function, the only permissions available for it are:\n%a"
            pname (env, p)
            ppermission_list (env, p)
      end
  | ExpectedType (t, var, d) ->
      bprintf
        "Could not extract from this subexpression (named %a) the following type:\n%a\n\
          some explanations follow:\n%a\n\nHere's a tentatively short error \
          message.\n%a\n%a"
        pnames (env, get_names env var)
        ptype (env, t)
        pderivation d
        Lexer.p (location env)
        pshort d
  | ExpectedPermission (t, d) ->
      bprintf
        "Could not extract the following perm:\n%a\nsome explanations follow:\n%a\n\
          \nHere's a tentatively short error message.\n%a\n%a"
        ptype (env, t)
        pderivation d
        Lexer.p (location env)
        pshort d
  | RecursiveOnlyForFunctions ->
      bprintf
        "Recursive definitions are enabled for functions only"
  | MissingField f ->
      bprintf
        "Field %a is missing in that constructor"
        Field.p f
  | ExtraField f ->
      bprintf
        "Field %a is superfluous in that constructor"
        Field.p f
  | NoTwoConstructors var ->
      begin match fold_var env var with
      | Some t ->
          bprintf
            "%a has type:\n%a\nIt is not a type with two constructors"
            pname (env, var)
            ptype (env, t)
      | None ->
          bprintf
            "%a has no suitable permission for a type with two constructors;\n\
              the only permissions available for it are:\n%a"
            pname (env, var)
            ppermission_list (env, var)
      end
  | NoSuchField (var, f) ->
      begin match fold_var env var with
      | Some t ->
          bprintf
            "%a has type:\n%a\nThere is no field named %a"
            pname (env, var)
            ptype (env, t)
            Field.p f
      | None ->
          bprintf
            "%a has no suitable permission with field %a;\n\
              the only permissions available for it are:\n%a"
            pname (env, var)
            Field.p f
            ppermission_list (env, var)
      end
  | CantAssignTag var ->
      begin match fold_var env var with
      | Some t ->
          bprintf
            "%a has type:\n%a\nWe can't assign a tag to it"
            pname (env, var)
            ptype (env, t)
      | None ->
          bprintf
            "%a has no suitable permission that would accept a tag update, \
              the only permissions available for it are:\n%a"
            pname (env, var)
            ppermission_list (env, var)
      end
  | MatchBadTuple p ->
      bprintf
        "Trying to match a tuple against a var whose only \
          permissions are:\n%a"
        ppermission_list (env, p)
  | MatchBadDatacon (p, datacon) ->
      bprintf
        "Trying to match data constructor %a against a var whose only \
          permissions are:\n%a"
        Datacon.p datacon
        ppermission_list (env, p)
  | NoSuchFieldInPattern (pat, field) ->
      bprintf
        "The pattern %a mentions field %a which is unknown for that branch"
        !internal_ppat (env, pat)
        Field.p field
  | BadPattern (pat, var) ->
      bprintf
        "Cannot match pattern %a against %a, the only permissions available for it are:\n%a"
        !internal_ppat (env, pat)
        pname (env, var)
        ppermission_list (env, var)
  | BadField (datacon, name) ->
      bprintf "This pattern mentions field %a but data constructor \
          %a has no such field"
        Field.p name
        Datacon.p datacon
  | AssignNotExclusive (t, datacon) ->
      bprintf
        "This value has type %a: constructor %a belongs to a data type that \
          is not defined as exclusive"
        ptype (env, t)
        Datacon.p datacon
  | FieldCountMismatch (t, datacon) ->
      bprintf
        "This value has type %a: constructor %a belongs to a data type that \
          does not have the same number of fields"
        ptype (env, t)
        Datacon.p datacon
  | NoMultipleArguments ->
      bprintf
        "Functions take only one (tuple) argument"
  | ResourceAllocationConflict var ->
      bprintf "Exclusive resource allocation conflict on %a"
        pnames (env, get_names env var);
  | UncertainMerge var ->
      bprintf "Merging distinct constructors into a nominal \
          type with type parameters, results are unpredictable, you should \
          consider providing annotations for %a"
        pnames (env, get_names env var)
  | ConflictingTypeAnnotations (t1, t2) ->
      bprintf "The context provides a type annotation, namely %a \
        but here is a type annotation, namely %a, that is conflicting the \
        context-provided type annotation"
        ptype (env, t1)
        ptype (env, t2);
  | BadTypeApplication var ->
      bprintf "Var %a does not have a polymorphic type, the only \
          permissions available for it are %a"
        pnames (env, get_names env var)
        ppermission_list (env, var)
  | IllKindedTypeApplication (t, k, k') ->
      bprintf "While applying type %a: this type has kind %a but \
          the sub-expression has a polymorphic type with kind %a"
        !internal_ptapp (env, t)
        MzPprint.pdoc (print_kind, k) 
        MzPprint.pdoc (print_kind, k');
  | NonExclusiveAdoptee t ->
      bprintf "Type %a cannot be adopted, because it is not exclusive"
        ptype (env, t)
  | NoAdoptsClause p ->
      bprintf "Trying to give/take to/from %a but this expression \
          cannot adopt; the only permissions available for it are %a"
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | NotDynamic p ->
      bprintf "Cannot take %a as it is not dynamic, the only \
          permissions available for it are %a"
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | NoSuitableTypeForAdopts (p, t) ->
      bprintf "Trying to give/take %a to/from some expression, but \
          the expression adopts %a and the only permissions available for %a are %a"
        pnames (env, get_names env p)
        ptype (env, t)
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | AdoptsNoAnnotation ->
      bprintf "In this “give e1 to e2” statement, please provide a \
          type annotation for e1"
  | NotMergingClauses (left_env, left_var, left_t, right_env, right_var, right_t) ->
      bprintf "While merging %a and %a, it turns out they have \
          different adopts clauses, namely %a and %a; I refuse to merge these, \
          so please annotate using identical adopts clauses"
        ptype (left_env, left_var)
        ptype (right_env, right_var)
        ptype (left_env, left_t)
        ptype (right_env, right_t)
  | NoSuchTypeInSignature (p, t, d) ->
      bprintf "This file exports a variable named %a, but it does \
        not have type %a, the only permissions available for it are: %a\n%a"
        pname (env, p)
        ptype (env, t)
        ppermission_list (env, p)
        pderivation d
  | DataTypeMismatchInSignature (x, reason) ->
      bprintf "Cannot match the definition of %a against the \
          signature because of: %s"
        Variable.p x
        reason
  | VarianceAnnotationMismatch ->
      bprintf "The variance annotations do not match the inferred ones"
  | ExportNotDuplicable v ->
      bprintf "This module exports variable %a with a non-duplicable type, \
          this is no longer allowed"
        Variable.p v
  | LocalType ->
      bprintf "This merge operation led us into trying to merge local types \
        (see tests/local-types.mz). Discarding these types."
  | Instantiated (v, t) ->
      bprintf "We instantiated %a as %a"
        Variable.p v
        ptype (env, t)
  | PackWithExists ->
      bprintf "You can only pack an existential"
  | SeveralWorkingFunctionTypes p ->
      bprintf "Several function types can be used for calling %a, \
        picking an arbitrary one."
        pnames (env, get_names env p)
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

let internal_extracterror = snd;;

let flags = Array.make 7 CError;;

(* When adding a new user-configurable error, there are *several* things to
 * update:
 *   - you should make the array above bigger;
 *   - you should update parsing/options.ml so that the default value is correct
 *   for the new message;
 *   - you should update testsuite.ml, the variables silent_warn_error and
 *   pedantic_warn_error should be refreshed.
 *)
let errno_of_error = function
  | UncertainMerge _ ->
      1
  | ResourceAllocationConflict _ ->
      2
  | NoMultipleArguments ->
      3
  | LocalType ->
      4
  | Instantiated _ ->
      5
  | SeveralWorkingFunctionTypes _ ->
      6
  | _ ->
      0 
;;

let may_raise_error env raw_error =
  let errno = errno_of_error raw_error in
  match flags.(errno) with
  | CError ->
      raise_error env raw_error
  | CWarning ->
      Log.warn "%a" print_error (env, raw_error)
  | CSilent ->
      ()
;;

let parse_warn_error s =
  let lexbuf = Ulexing.from_utf8_string s in
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised Grammar.warn_error_list in
  let user_flags =
    try
      the_parser (fun _ -> Lexer.token lexbuf)
    with Ulexing.Error | Grammar.Error ->
      Log.error "Malformed warn-error list"
  in
  List.iter (fun (f, (l, h)) ->
    if l < 0 || h >= Array.length flags then
      Log.error "No error for that number";
    for i = l to h do
      flags.(i) <- f
    done;
  ) user_flags
;;
