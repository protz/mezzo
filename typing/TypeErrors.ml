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
  | CyclicDependency of Module.name
  | NotAFunction of point
  | HasFlexible of typ
  | ExpectedType of typ * point
  | RecursiveOnlyForFunctions
  | MissingField of Field.name
  | ExtraField of Field.name
  | NoSuchField of point * Field.name
  | FieldMismatch of typ * Datacon.name
  | CantAssignTag of point
  | NoSuchFieldInPattern of pattern * Field.name
  | BadPattern of pattern * point
  | BadField of Datacon.name * Field.name
  | SubPattern of pattern
  | NoTwoConstructors of point
  | MatchBadDatacon of point * Datacon.name
  | MatchBadTuple of point
  | NoSuchPermission of typ
  | AssignNotExclusive of typ * Datacon.name
  | FieldCountMismatch of typ * Datacon.name
  | NoMultipleArguments
  | ResourceAllocationConflict of point
  | UncertainMerge of point
  | ConflictingTypeAnnotations of typ * typ
  | IllKindedTypeApplication of tapp * kind * kind
  | BadTypeApplication of point
  | PolymorphicFunctionCall
  | BadFactForAdoptedType of point * typ * fact
  | NoAdoptsClause of point
  | NotDynamic of point
  | NoSuitableTypeForAdopts of point * typ
  | AdoptsNoAnnotation
  | NotMergingClauses of env * typ * typ * env * typ * typ
  | MissingFieldInSignature of Variable.name
  | NoSuchTypeInSignature of point * typ
  | DataTypeMismatchInSignature of Variable.name * string
  | NotExclusiveOwns of point
  | UnsatisfiableConstraint of duplicity_constraint list

exception TypeCheckerError of error

let raise_error env e =
  raise (TypeCheckerError (env, e))
;;

(* -------------------------------------------------------------------------- *)

(* For pretty-printing. *)

exception NotFoldable

(** [fold_point env point] tries to find (hopefully) one "main" type for [point], by
    folding back its "main" type [t] into a form that's suitable for one
    thing, and one thing only: printing. *)
let rec fold_point (env: env) (point: point): (env * typ) option =
  let perms = get_permissions env point in
  let perms = List.filter
    (function
      | TySingleton (TyOpen p) when same env p point ->
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
        let env = replace_term env point (function binding ->
          { binding with permissions = [TyDynamic] }
        ) in
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
      begin match fold_point env p with
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

let fold_point env t =
  Option.map snd (fold_point env t)
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
      begin match fold_point env p with
      | Some t ->
          Printf.bprintf buf
            "%a %a is not a function, it has type:\n%a"
            Lexer.p env.location
            pname (env, p)
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a is not a function, the only permissions available for it are:\n%a"
            Lexer.p env.location
            pname (env, p)
            ppermission_list (env, p)
      end
  | NoSuchPermission t ->
      Printf.bprintf buf
        "%a unable to extract the following permission:\n%a"
        Lexer.p env.location
        ptype (env, t);
  | HasFlexible t ->
      Printf.bprintf buf
        "%a the following type still contains flexible variables:\n%a"
        Lexer.p env.location
        ptype (env, t);
  | ExpectedType (t, point) ->
      let t1 = fold_type env t in
      let t2 = fold_point env point in
      begin match t1, t2 with
      | Some t1, Some t2 -> (* #winning *)
          Printf.bprintf buf
            "%a expected an expression of type:\n%a\nbut this expression has type:\n%a\n"
            Lexer.p env.location
            ptype (env, t1)
            ptype (env, t2)
      | _ ->
          Printf.bprintf buf
            "%a expected an argument of type:\n%a but the only permissions available for %a are:\n%a"
            Lexer.p env.location
            ptype (env, t) pname (env, point)
            ppermission_list (env, point)
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
  | NoTwoConstructors point ->
      begin match fold_point env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type:\n%a\nIt is not a type with two constructors"
            Lexer.p env.location
            pname (env, point)
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission for a type with two constructors;\n\
              the only permissions available for it are:\n%a"
            Lexer.p env.location
            pname (env, point)
            ppermission_list (env, point)
      end
  | NoSuchField (point, f) ->
      begin match fold_point env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type:\n%aThere is no field named %a"
            Lexer.p env.location
            pname (env, point)
            ptype (env, t)
            Field.p f
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission with field %a;\n\
             the only permissions available for it are:\n%a"
            Lexer.p env.location
            pname (env, point)
            Field.p f
            ppermission_list (env, point)
      end
  | FieldMismatch (t, datacon) ->
      Printf.bprintf buf
        "%a user-provided type:\n%a\ndoes not match the fields of data constructor %a"
        Lexer.p env.location
        ptype (env, t)
        Datacon.p datacon
  | CantAssignTag point ->
      begin match fold_point env point with
      | Some t ->
          Printf.bprintf buf
            "%a %a has type:\n%a\nWe can't assign a tag to it"
            Lexer.p env.location
            pname (env, point)
            ptype (env, t)
      | None ->
          Printf.bprintf buf
            "%a %a has no suitable permission that would accept a tag update, \
              the only permissions available for it are:\n%a"
            Lexer.p env.location
            pname (env, point)
            ppermission_list (env, point)
      end
  | SubPattern pat ->
      Printf.bprintf buf
        "%a there's a sub-constraint in that pattern, not allowed: %a"
        Lexer.p env.location
        ppat (env, pat)
  | MatchBadTuple p ->
      Printf.bprintf buf
        "%a trying to match a tuple against a point whose only \
          permissions are:\n%a"
        Lexer.p env.location
        ppermission_list (env, p)
  | MatchBadDatacon (p, datacon) ->
      Printf.bprintf buf
        "%a trying to match data constructor %a against a point whose only \
          permissions are:\n%a"
        Lexer.p env.location
        Datacon.p datacon
        ppermission_list (env, p)
  | NoSuchFieldInPattern (pat, field) ->
      Printf.bprintf buf
        "%a the pattern %a mentions field %a which is unknown for that branch"
        Lexer.p env.location
        ppat (env, pat)
        Field.p field
  | BadPattern (pat, point) ->
      Printf.bprintf buf
        "%a cannot match pattern %a against %a, the only permissions available for it are:\n%a"
        Lexer.p env.location
        ppat (env, pat)
        pname (env, point)
        ppermission_list (env, point)
  | BadField (datacon, name) ->
      Printf.bprintf buf "%a this pattern mentions field %a but data constructor \
          %a has no such field"
        Lexer.p env.location
        Field.p name
        Datacon.p datacon

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
        pnames (env, get_names env point);
  | UncertainMerge point ->
      Printf.bprintf buf "%a merging distinct constructors into a nominal \
          type with type parameters, results are unpredictable, you should \
          consider providing annotations for %a"
        Lexer.p env.location
        pnames (env, get_names env point)
  | ConflictingTypeAnnotations (t1, t2) ->
      Printf.bprintf buf "%a the context provides a type annotation, namely %a \
        but here is a type annotation, namely %a, that is conflicting the \
        context-provided type annotation"
        Lexer.p env.location
        ptype (env, t1)
        ptype (env, t2);
  | BadTypeApplication point ->
      Printf.bprintf buf "%a point %a does not have a polymorphic type, the only \
          permissions available for it are %a"
        Lexer.p env.location
        pnames (env, get_names env point)
        ppermission_list (env, point)
  | IllKindedTypeApplication (t, k, k') ->
      Printf.bprintf buf "%a while applying type %a: this type has kind %a but \
          the sub-expression has a polymorphic type with kind %a"
        Lexer.p env.location
        pdoc ((fun t -> ExprPrinter.print_tapp env t), t)
        pdoc (print_kind, k) 
        pdoc (print_kind, k');
  | PolymorphicFunctionCall ->
      Printf.bprintf buf "%a this is a polymorphic function call, results are \
          undefined; consider using a type application"
        Lexer.p env.location
  | BadFactForAdoptedType (p, t, f) ->
      Printf.bprintf buf "%a type %a cannot adopt type %a because it is not \
          marked as exclusive but %a"
        Lexer.p env.location
        pnames (env, get_names env p)
        ptype (env, t)
        pfact f
  | NoAdoptsClause p ->
      Printf.bprintf buf "%a trying to give/take to/from %a but this expression \
          cannot adopt; the only permissions available for it are %a"
        Lexer.p env.location
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | NotDynamic p ->
      Printf.bprintf buf "%a cannot take %a as it is not dynamic, the only \
          permissions available for it are %a"
        Lexer.p env.location
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | NoSuitableTypeForAdopts (p, t) ->
      Printf.bprintf buf "%a trying to give/take %a to/from some expression, but \
          the expression adopts %a and the only permissions available for %a are %a"
        Lexer.p env.location
        pnames (env, get_names env p)
        ptype (env, t)
        pnames (env, get_names env p)
        ppermission_list (env, p)
  | AdoptsNoAnnotation ->
      Printf.bprintf buf "%a in this “give e1 to e2” statement, please provide a \
          type annotation for e1"
        Lexer.p env.location;
  | NotMergingClauses (left_env, left_point, left_t, right_env, right_point, right_t) ->
      Printf.bprintf buf "%a while merging %a and %a, it turns out they have \
          different adopts clauses, namely %a and %a; I refuse to merge these, \
          so please annotate using identical adopts clauses"
        Lexer.p env.location
        ptype (left_env, left_point)
        ptype (right_env, right_point)
        ptype (left_env, left_t)
        ptype (right_env, right_t)
  | MissingFieldInSignature name ->
      Printf.bprintf buf "%a this file does not export a variable named %a"
        Lexer.p env.location
        Variable.p name
  | NoSuchTypeInSignature (p, t) ->
      Printf.bprintf buf "%a this file exports a variable named %a, but it does \
        not have type %a, the only permissions available for it are: %a"
        Lexer.p env.location
        pname (env, p)
        ptype (env, t)
        ppermission_list (env, p)
  | DataTypeMismatchInSignature (x, reason) ->
      Printf.bprintf buf "%a cannot match the definition of %a against the \
          signature because of: %s"
        Lexer.p env.location
        Variable.p x
        reason
  | NotExclusiveOwns p ->
      Printf.bprintf buf "%a %a is not exclusive so it canno hold anything; \
          the only permissions available for it are %a"
        Lexer.p env.location
        pname (env, p)
        ppermission_list (env, p)
  | CyclicDependency m ->
      Printf.bprintf buf "There is a cyclic dependency on module %a" Module.p m
  | UnsatisfiableConstraint cs ->
      Printf.bprintf buf "%a one of the following constraints cannot be satisfied: %a"
        Lexer.p env.location
        pconstraints (env, cs)
;;
