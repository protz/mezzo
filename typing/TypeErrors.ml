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

open Types
open Expressions

type error = env * raw_error

and raw_error =
  | NotAFunction of point
  | HasFlexible of typ
  | ExpectedType of typ * point
  | RecursiveOnlyForFunctions
  | MissingField of Field.name
  | ExtraField of Field.name
  | NoSuchField of point * Field.name
  | CantAssignTag of point
  | NoSuchFieldInPattern of pattern * Field.name
  | SubPattern of pattern
  | NoTwoConstructors of point
  | NotNominal of point
  | MatchBadDatacon of typ * Datacon.name
  | MatchBadPattern of pattern
  | NoSuchPermission of typ
  | AssignNotExclusive of typ * Datacon.name
  | FieldCountMismatch of typ * Datacon.name
  | NoMultipleArguments
  | ResourceAllocationConflict of point
  | UncertainMerge of point
  | ConflictingTypeAnnotations of typ * typ
  | IllKindedTypeApplication of typ * kind * kind
  | BadTypeApplication of point
  | PolymorphicFunctionCall
  | BadFactForAdoptedType of point * typ * fact
  | NoAdoptsClause of point
  | NoSuitableTypeForAdopts of point * typ
  | AdoptsNoAnnotation
  | NotMergingClauses of env * typ * typ * env * typ * typ
  | MissingFieldInSignature of Variable.name
  | NoSuchTypeInSignature of Variable.name * typ
  | DataTypeMismatchInSignature of Variable.name

exception TypeCheckerError of error

let raise_error env e =
  raise (TypeCheckerError (env, e))
;;

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
      let fname, fbinder = find_term env p in
      begin match Permissions.fold env p with
      | Some t ->
          Printf.bprintf buf
            "%a %a is not a function, it has type %a"
            Lexer.p env.location
            pvar fname
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a is not a function, the only permissions available for it are %a"
            Lexer.p env.location
            pvar fname
            pdoc (print_permission_list, (env, fbinder))
      end
  | NoSuchPermission t ->
      Printf.bprintf buf
        "%a unable to extract the following permission: %a"
        Lexer.p env.location
        ptype (env, t);
  | HasFlexible t ->
      Printf.bprintf buf
        "%a the following type still contains flexible variables: %a"
        Lexer.p env.location
        ptype (env, t);
  | ExpectedType (t, point) ->
      let xname, xbinder = find_term env point in
      let t1 = Permissions.fold_type env t in
      let t2 = Permissions.fold env point in
      begin match t1, t2 with
      | Some t1, Some t2 -> (* #winning *)
          Printf.bprintf buf
            "%a expected a subexpression of type %a but it has type %a"
            Lexer.p env.location
            ptype (env, t1)
            ptype (env, t2)
      | _ ->
          Printf.bprintf buf
            "%a expected an argument of type %a but the only permissions available for %a are %a"
            Lexer.p env.location
            ptype (env, t) pvar xname
            pdoc (print_permission_list, (env, xbinder))
      end
  | RecursiveOnlyForFunctions ->
      Printf.bprintf buf
        "%a recursive definitions are enabled for functions only"
        Lexer.p env.location
  | MissingField f ->
      Printf.bprintf buf
        "%a field %a is missing in that constructor"
        Lexer.p env.location
        Field.p f
  | ExtraField f ->
      Printf.bprintf buf
        "%a field %a is superfluous in that constructor"
        Lexer.p env.location
        Field.p f
  | NotNominal point ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, we can't match on it"
            Lexer.p env.location
            pvar name
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no permission with a nominal type suitable for matching, \
              the only permissions available for it are %a"
            Lexer.p env.location
            pvar name
            pdoc (print_permission_list, (env, binder))
      end
  | NoTwoConstructors point ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, is is not a type with two constructors"
            Lexer.p env.location
            pvar name
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission for a type with two constructors, \
              the only permissions available for it are %a"
            Lexer.p env.location
            pvar name
            pdoc (print_permission_list, (env, binder))
      end
  | NoSuchField (point, f) ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, which doesn't have a field named %a"
            Lexer.p env.location
            pvar name
            ptype (env, t)
            Field.p f
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission with field %a, the only permissions \
              available for it are %a"
            Lexer.p env.location
            pvar name
            Field.p f
            pdoc (print_permission_list, (env, binder))
      end
   | CantAssignTag point ->
      let name, binder = find_term env point in
      begin match Permissions.fold env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type %a, we can't assign a tag to it"
            Lexer.p env.location
            pvar name
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission that would accept a tag update, \
              the only permissions available for it are %a"
            Lexer.p env.location
            pvar name
            pdoc (print_permission_list, (env, binder))
      end
  | SubPattern pat ->
      Printf.bprintf buf
        "%a there's a sub-constraint in that pattern, not allowed: %a"
        Lexer.p env.location
        ppat (env, pat)
  | MatchBadDatacon (t, datacon) ->
      Printf.bprintf buf
        "%a matching on a value with type %a: it has no constructor named %a"
        Lexer.p env.location
        ptype (env, t)
        Datacon.p datacon
  | MatchBadPattern pat ->
      Printf.bprintf buf
        "%a the pattern %a is not valid inside a match; only matches on data \
          constructors are allowed"
        Lexer.p env.location
        ppat (env, pat)
  | NoSuchFieldInPattern (pat, field) ->
      Printf.bprintf buf
        "%a the pattern %a mentions field %a which is unknown for that branch"
        Lexer.p env.location
        ppat (env, pat)
        Field.p field
  | AssignNotExclusive (t, datacon) ->
      Printf.bprintf buf
        "%a this value has type %a: constructor %a belongs to a data type that \
          is not defined as exclusive"
        Lexer.p env.location
        ptype (env, t)
        Datacon.p datacon
  | FieldCountMismatch (t, datacon) ->
      Printf.bprintf buf
        "%a this value has type %a: constructor %a belongs to a data type that \
          does not have the same number of fields"
        Lexer.p env.location
        ptype (env, t)
        Datacon.p datacon
  | NoMultipleArguments ->
      Printf.bprintf buf
        "%a functions take only one tuple argument in HaMLet"
        Lexer.p env.location
  | ResourceAllocationConflict point ->
      Printf.bprintf buf "%a exclusive resource allocation conflict on %a"
        Lexer.p env.location
        TypePrinter.pnames (get_names env point);
  | UncertainMerge point ->
      Printf.bprintf buf "%a merging distinct constructors into a nominal \
          type with type parameters, results are unpredictable, you should \
          consider providing annotations for %a"
        Lexer.p env.location
        TypePrinter.pnames (get_names env point)
  | ConflictingTypeAnnotations (t1, t2) ->
      Printf.bprintf buf "%a the context provides a type annotation, namely %a \
        but here is a type annotation, namely %a, that is conflicting the \
        context-provided type annotation"
        Lexer.p env.location
        TypePrinter.ptype (env, t1)
        TypePrinter.ptype (env, t2);
  | BadTypeApplication point ->
      let _, binder = find_term env point in
      Printf.bprintf buf "%a point %a does not have a polymorphic type, the only \
          permissions available for it are %a"
        Lexer.p env.location
        TypePrinter.pnames (get_names env point)
        TypePrinter.pdoc (TypePrinter.print_permission_list, (env, binder));
  | IllKindedTypeApplication (t, k, k') ->
      Printf.bprintf buf "%a while applying type %a: this type has kind %a but \
          the sub-expression has a polymorphic type with kind %a"
        Lexer.p env.location
        TypePrinter.ptype (env, t)
        TypePrinter.pdoc (TypePrinter.print_kind, k) 
        TypePrinter.pdoc (TypePrinter.print_kind, k');
  | PolymorphicFunctionCall ->
      Printf.bprintf buf "%a this is a polymorphic function all, results are \
          undefined; consider using a type application"
        Lexer.p env.location
  | BadFactForAdoptedType (p, t, f) ->
      Printf.bprintf buf "%a type %a cannot adopt type %a because it is not \
          marked as exclusive but %a"
        Lexer.p env.location
        TypePrinter.pnames (get_names env p)
        TypePrinter.ptype (env, t)
        TypePrinter.pfact f
  | NoAdoptsClause p ->
      let _, binder = find_term env p in
      Printf.bprintf buf "%a trying to give/take to/from %a but this expression \
          cannot adopt; the only permissions available for it are %a"
        Lexer.p env.location
        TypePrinter.pnames (get_names env p)
        TypePrinter.pdoc (TypePrinter.print_permission_list, (env, binder));
  | NoSuitableTypeForAdopts (p, t) ->
      let _, binder = find_term env p in
      Printf.bprintf buf "%a trying to give/take %a to/from some expression, but \
          the expression adopts %a and the only permissions available for %a are %a"
        Lexer.p env.location
        TypePrinter.pnames (get_names env p)
        TypePrinter.ptype (env, t)
        TypePrinter.pnames (get_names env p)
        TypePrinter.pdoc (TypePrinter.print_permission_list, (env, binder));
  | AdoptsNoAnnotation ->
      Printf.bprintf buf "%a in this “give e1 to e2” statement, please provide a \
          type annotation for e1"
        Lexer.p env.location;
  | NotMergingClauses (left_env, left_point, left_t, right_env, right_point, right_t) ->
      Printf.bprintf buf "%a while merging %a and %a, it turns out they have \
          different adopts clauses, namely %a and %a; I refuse to merge these, \
          so please annotate using identical adopts clauses"
        Lexer.p env.location
        TypePrinter.ptype (left_env, left_point)
        TypePrinter.ptype (right_env, right_point)
        TypePrinter.ptype (left_env, left_t)
        TypePrinter.ptype (right_env, right_t)
  | MissingFieldInSignature name ->
      Printf.bprintf buf "%a this file does not export a variable named %a"
        Lexer.p env.location
        Variable.p name
  | NoSuchTypeInSignature (x, t) ->
      Printf.bprintf buf "%a this file export a variable named %a, but it does \
        not have type %a"
        Lexer.p env.location
        Variable.p x
        TypePrinter.ptype (env, t)
  | DataTypeMismatchInSignature x ->
      Printf.bprintf buf "%a the definitions of type %a differ in the signature \
          and the implementation"
        Lexer.p env.location
        Variable.p x
;;
