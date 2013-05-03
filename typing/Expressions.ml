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

(* This file contains our internal syntax for expressions. *)

open Kind
open TypeCore
open DeBruijn
open Types
module RAL = RandomAccessList (* TEMPORARY *)

(* ---------------------------------------------------------------------------- *)

(* Definitions borrowed from SurfaceSyntax. *)

type tag_update_info =
    SurfaceSyntax.tag_update_info

type field =
    SurfaceSyntax.field

(* ---------------------------------------------------------------------------- *)

(* Patterns *)

(* The De Bruijn numbering is defined according to a depth-first traversal of
 * the pattern: the first variable encountered will have index 0, and so on. *)
type pattern =
  (* x *)
  | PVar of Variable.name * location
        (* TEMPORARY is the name important here, or just a hint? *)
  (* (x₁, …, xₙ) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of resolved_datacon * (Field.name * pattern) list
  (* Once the variables in a pattern have been bound, they may be replaced by
   * [POpen]s so that we know how to speak about the bound variables. *)
  | POpen of var
  | PAs of pattern * pattern
  | PAny

(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = SurfaceSyntax.rec_flag = Nonrecursive | Recursive

type expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v, bound *)
  | EVar of db_index
  (* v, free *)
  | EOpen of var
  (* builtin foo *)
  | EBuiltin of string
  (* let rec pat = expr and pat' = expr' in expr *)
  | ELet of rec_flag * patexpr list * expression
  (* [a, ..., a] e *)
  | EBigLambdas of (type_binding * flavor) list * expression
  (* lambda (x: τ): τ -> e *)
  (* A lambda binds exactly one variable, which has de Bruijn index 0.
     The scope of this variable is the function body, [e].
     This is in contrast with the surface syntax, where many variables
     can be bound, and the argument type is interpreted as a pattern. *)
  | ELambda of typ * typ * expression
  (* v.f <- e *)
  | EAssign of expression * field * expression
  (* tag of v <- Foo *)
  | EAssignTag of expression * resolved_datacon * tag_update_info
  (* v.f *)
  | EAccess of expression * field
  (* e₁ e₂ *)
  | EApply of expression * expression
  (* e [τ₁, …, τₙ] *)
  | ETApply of expression * tapp * kind
  (* match e with pᵢ -> eᵢ *)
  | EMatch of bool * expression * patexpr list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of resolved_datacon * (Field.name * expression) list
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of bool * expression * expression * expression
  | ELocated of expression * location
  | EInt of int
  (* Explanations *)
  | EExplained of expression
  (* Adoption/abandon *)
  | EGive of expression * expression
  | ETake of expression * expression
  | EOwns of expression * expression
  (* fail *)
  | EFail

and tapp =
  | Ordered of typ
  | Named of Variable.name * typ

and patexpr =
  (* A binding is made up of a pattern, an optional type annotation for the
   * entire pattern (desugared), and an expression. *)
  pattern * expression

(* The grammar below doesn't enforce the “only variables are allowed on the
 * left-hand side of a let rec” rule. We'll see to that later. Here too, the
 * order of the bindings is significant: if the binding is recursive, the
 * variables in all the patterns are collected in order before type-checking the
 * expressions. *)

type definitions =
  location * rec_flag * (pattern * expression) list

type sig_item =
  Variable.name * typ

type toplevel_item =
  | DataTypeGroup of data_type_group
  | ValueDefinitions of definitions
  | ValueDeclaration of sig_item

type implementation =
  toplevel_item list

type interface =
  toplevel_item list

let e_unit =
  ETuple []
;;

let p_unit =
  PTuple []
;;

(* ---------------------------------------------------------------------------- *)

(* Moar fun with De Bruijn. *)

(* TEMPORARY since type variables and expression variables belong to the same
   namespace, I believe that there is some code duplication that we could
   eliminate here. *)

let map_tapp f = function
  | Ordered t ->
      Ordered (f t)
  | Named (x, t) ->
      Named (x, f t)
;;

(* [collect_pattern] returns the list of bindings present in the pattern. The
 * binding with index [i] in the returned list has De Bruijn index [i] in the
 * bound term. *)
let collect_pattern (p: pattern): ((Variable.name * location) list) =
  let rec collect_pattern acc = function
  | PVar (name, p) ->
      (name, p) :: acc
  | PTuple patterns ->
      List.fold_left collect_pattern acc patterns
  | PConstruct (_, fields) ->
      let patterns = snd (List.split fields) in
      List.fold_left collect_pattern acc patterns
  | POpen _ ->
      assert false
  | PAs (p1, p2) ->
      List.fold_left collect_pattern acc [p1; p2]
  | PAny ->
      acc
  in
  (* Return the names in reading order, i.e. left-to-right. *)
  List.rev (collect_pattern [] p)
;;

(* How many binders in this declaration group? *)
let n_defs (_, _, patexprs) =
  let patterns, _ = List.split patexprs in
  List.length (collect_pattern (PTuple patterns))

(* [psubst pat vars] replaces names in [pat] as it goes, by popping vars off
 * the front of [vars]. *)
let rec psubst (pat: pattern) (vars: var list) =
  match pat with
  | PVar _ ->
      begin match vars with
      | hd :: tl ->
          POpen hd, tl
      | _ ->
          Log.error "Wrong variable count for [psubst]"
      end

  | POpen _ ->
      Log.error "You ran a pattern through [psubst] twice"

  | PTuple pats ->
      let pats, vars = List.fold_left (fun (pats, vars) pat ->
          let pat, vars = psubst pat vars in
          pat :: pats, vars
        ) ([], vars) pats
      in
      let pats = List.rev pats in
      PTuple pats, vars

  | PConstruct (datacon, fieldpats) ->
      let fieldpats, vars = List.fold_left (fun (fieldpats, vars) (field, pat) ->
          let pat, vars = psubst pat vars in
          (field, pat) :: fieldpats, vars
        ) ([], vars) fieldpats
      in
      let fieldpats = List.rev fieldpats in
      PConstruct (datacon, fieldpats), vars

  | PAs (p1, p2) ->
      let pats, vars = List.fold_left (fun (pats, vars) pat ->
          let pat, vars = psubst pat vars in
          pat :: pats, vars
        ) ([], vars) [p1; p2]
      in
      let pats = List.rev pats in
      let p1, p2 = match pats with [p1; p2] -> p1, p2 | _ -> assert false in
      PAs (p1, p2), vars

  | PAny ->
      PAny, vars
;;


(* [tsubst_pat t2 i p1] substitutes type [t2] for index [i] in pattern [p1]. *)
let tsubst_pat (t2: typ) (i: db_index) (p1: pattern): pattern =
  let rec tsubst_pat t2 p1 =
    match p1 with
    | PVar _
    | POpen _
    | PAny ->
        p1
    | PTuple ps ->
        PTuple (List.map (tsubst_pat t2) ps)
    | PAs (p1, p2) ->
        PAs (tsubst_pat t2 p1, tsubst_pat t2 p2)
    | PConstruct ((t, dc), fieldpats) ->
        let t = tsubst t2 i t in
        let fieldpats = List.map (fun (f, p) -> f, tsubst_pat t2 p) fieldpats in
        PConstruct ((t, dc), fieldpats)
  in
  tsubst_pat t2 p1
;;


(* [tsubst_patexprs t2 i rec_flag pat_exprs] substitutes type [t2] for index [i]
 * in the list of pattern-expressions [pat_exprs], defined recursively or not,
 * depending on [rec_flag]. *)
let rec tsubst_patexprs t2 i rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let patterns = List.map (tsubst_pat t2 i) patterns in
  let names = List.fold_left (fun acc p ->
    collect_pattern p :: acc) [] patterns
  in
  let names = List.flatten names in
  let n = List.length names in
  (* TEMPORARY looks as if only the length of [names] matters; use [n_defs] *)
  let expressions = match rec_flag with
    | Recursive ->
        List.map (tsubst_expr t2 (i + n)) expressions
    | Nonrecursive ->
        List.map (tsubst_expr t2 i) expressions
  in
  n, List.combine patterns expressions


(* [tsubst_expr t2 i e] substitutes type [t2] for index [i] in expression [e]. *)
and tsubst_expr t2 i e =
  match e with
  | EConstraint (e, t) ->
      EConstraint (tsubst_expr t2 i e, tsubst t2 i t)

  | EVar _
  | EOpen _ 
  | EBuiltin _ ->
      e

  | ELet (rec_flag, patexprs, body) ->
      let n, patexprs = tsubst_patexprs t2 i rec_flag patexprs in
      let body = tsubst_expr t2 (i + n) body in
      ELet (rec_flag, patexprs, body)

  | EBigLambdas (xs, e) ->
      let n = List.length xs in
      EBigLambdas (xs, tsubst_expr t2 (i + n) e)

  | ELambda (arg, return_type, body) ->
      let arg = tsubst t2 i arg in
      let return_type = tsubst t2 i return_type in
      let body = tsubst_expr t2 (i + 1) body in
      ELambda (arg, return_type, body)

  | EAssign (e1, field, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EAssign (e1, field, e2)

  | EAssignTag (e1, (t, dc), info) ->
      let e1 = tsubst_expr t2 i e1 in
      EAssignTag (e1, (tsubst t2 i t, dc), info)

  | EAccess (e1, field) ->
      let e1 = tsubst_expr t2 i e1 in
      EAccess (e1, field)

  | EApply (f, arg) ->
      let f = tsubst_expr t2 i f in
      let arg = tsubst_expr t2 i arg in
      EApply (f, arg)

  | ETApply (f, arg, k) ->
      let f = tsubst_expr t2 i f in
      let arg = map_tapp (tsubst t2 i) arg in
      ETApply (f, arg, k)

  | EMatch (b, e, patexprs) ->
      let e = tsubst_expr t2 i e in
      let patexprs = List.map (fun (pat, expr) ->
          let pat = tsubst_pat t2 i pat in
          let names = collect_pattern pat in
          let n = List.length names in
          (* TEMPORARY looks as if only the length of [names] matters; use [n_defs] *)
          pat, tsubst_expr t2 (i + n) expr
        ) patexprs
      in
      EMatch (b, e, patexprs)

  | ETuple exprs ->
      let exprs = List.map (tsubst_expr t2 i) exprs in
      ETuple exprs

  | EConstruct ((t, dc), fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, tsubst_expr t2 i expr) fieldexprs
      in
      EConstruct ((tsubst t2 i t, dc), fieldexprs)

  | EIfThenElse (b, e1, e2, e3) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      let e3 = tsubst_expr t2 i e3 in
      EIfThenElse (b, e1, e2, e3)

  | ELocated (e, p) ->
      let e = tsubst_expr t2 i e in
      ELocated (e, p)

  | EInt _ ->
      e

  | EExplained e ->
      let e = tsubst_expr t2 i e in
      EExplained e

  | ETake (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      ETake (e1, e2)

  | EGive (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EGive (e1, e2)

  | EOwns (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EOwns (e1, e2)

  | EFail ->
      EFail


(* [tsubst_def t2 i defs] substitutes type [t2] for index [i] in a definition
 * group [defs]. *)
and tsubst_def t2 i (loc, rec_flag, patexprs) =
  let _, patexprs = tsubst_patexprs t2 i rec_flag patexprs in
  loc, rec_flag, patexprs

let rec tsubst_toplevel_items t2 i toplevel_items =
  match toplevel_items with
  | DataTypeGroup group :: toplevel_items ->
      let n = List.length group.group_items in
      let group =
        if group.group_recursive = Recursive then
          (* Since the type bindings are all mutually recursive, they're considered
           * to be all bound in the data type groups. *)
          tsubst_data_type_group t2 (i + n) group
        else 
          tsubst_data_type_group t2 i group
      in
      let toplevel_items = tsubst_toplevel_items t2 (i + n) toplevel_items in
      DataTypeGroup group :: toplevel_items
  | ValueDefinitions defs :: toplevel_items ->
      let defs = tsubst_def t2 i defs in
      let n = n_defs defs in
      let toplevel_items = tsubst_toplevel_items t2 (i + n) toplevel_items in
      ValueDefinitions defs :: toplevel_items
  | ValueDeclaration (x, t) :: toplevel_items ->
      let t = tsubst t2 i t in
      let toplevel_items = tsubst_toplevel_items t2 (i + 1) toplevel_items in
      ValueDeclaration (x, t) :: toplevel_items
  | [] ->
      []
;;

(* [esubst_patexprs e2 i rec_flag pat_exprs] substitutes expression [e2] for index [i]
 * in the list of pattern-expressions [pat_exprs], defined recursively or not,
 * depending on [rec_flag]. *)
let rec esubst_patexprs e2 i rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let names = List.fold_left (fun acc p ->
    collect_pattern p :: acc) [] patterns
  in
  let names = List.flatten names in
  let n = List.length names in
  (* TEMPORARY looks as if only the length of [names] matters; use [n_defs] *)
  let expressions = match rec_flag with
    | Recursive ->
        List.map (esubst e2 (i + n)) expressions
    | Nonrecursive ->
        List.map (esubst e2 i) expressions
  in
  n, List.combine patterns expressions

(* [esubst e2 i e1] substitutes expression [e2] for index [i] in expression [e1]. *)
and esubst e2 i e1 =
  match e1 with
  | EConstraint (e, t) ->
      let e = esubst e2 i e in
      EConstraint (e, t)

  | EVar index ->
      if i = index then
        e2
      else
        e1

  | EOpen _
  | EBuiltin _ ->
      e1

  | ELet (rec_flag, patexprs, body) ->
      let n, patexprs = esubst_patexprs e2 i rec_flag patexprs in
      let body = esubst e2 (i + n) body in
      ELet (rec_flag, patexprs, body)

  | EBigLambdas (xs, e) ->
      let n = List.length xs in
      EBigLambdas (xs, esubst e2 (i + n) e)

  | ELambda (arg, return_type, body) ->
      ELambda (arg, return_type, esubst e2 (i + 1) body)

  | EAssign (e, f, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EAssign (e, f, e')

  | EAssignTag (e, d, info) ->
      let e = esubst e2 i e in
      EAssignTag (e, d, info)

  | EAccess (e, f) ->
      let e = esubst e2 i e in
      EAccess (e, f)

  | EApply (f, arg) ->
      let f = esubst e2 i f in
      let arg = esubst e2 i arg in
      EApply (f, arg)

  | ETApply (f, arg, k) ->
      let f = esubst e2 i f in
      ETApply (f, arg, k)

  | EMatch (b, e, patexprs) ->
      let e = esubst e2 i e in
      let patexprs = List.map (fun (pat, expr) ->
        let names = collect_pattern pat in
        let n = List.length names in
        (* TEMPORARY looks as if only the length of [names] matters; use [n_defs] *)
        let expr = esubst e2 (i + n) expr in
        pat, expr) patexprs
      in
      EMatch (b, e, patexprs)

  | ETuple exprs ->
      let exprs = List.map (esubst e2 i) exprs in
      ETuple exprs

  | EConstruct (name, fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, esubst e2 i expr) fieldexprs
      in
      EConstruct (name, fieldexprs)

  | EIfThenElse (b, e, e', e'') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      let e'' = esubst e2 i e'' in
      EIfThenElse (b, e, e', e'')


  | ELocated (e, p) ->
      let e = esubst e2 i e in
      ELocated (e, p)

  | EInt _ ->
      e1

  | EExplained e ->
      let e = esubst e2 i e in
      EExplained e

  | ETake (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      ETake (e, e')

  | EGive (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EGive (e, e')

  | EOwns (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EOwns (e, e')

  | EFail ->
      EFail

(* [esubst_def e2 i decls] substitutes expression [e2] for index [i] in a
 * definition group [defs]. *)
and esubst_def e2 i (loc, rec_flag, patexprs) =
  let _, patexprs = esubst_patexprs e2 i rec_flag patexprs in
  loc, rec_flag, patexprs

let rec esubst_toplevel_items e2 i toplevel_items =
  match toplevel_items with
  | DataTypeGroup group :: toplevel_items ->
      (* Nothing to substitute here, only binders to cross. *)
      let n = List.length group.group_items in
      let toplevel_items = esubst_toplevel_items e2 (i + n) toplevel_items in
      DataTypeGroup group :: toplevel_items
  | ValueDefinitions defs :: toplevel_items ->
      let defs = esubst_def e2 i defs in
      let n = n_defs defs in
      let toplevel_items = esubst_toplevel_items e2 (i + n) toplevel_items in
      ValueDefinitions defs :: toplevel_items
  | (ValueDeclaration _ as toplevel_item) :: toplevel_items ->
      let toplevel_items = esubst_toplevel_items e2 (i + 1) toplevel_items in
      toplevel_item :: toplevel_items
  | [] ->
      []
;;


(* The idea is that when you bind, say, a list of variables of arbitrary kind
 * (through type bindings, or a pattern in a let-binding), you want to
 * perform the substitutions on whatever's under the bound variables. The
 * functions that perform the binding are [bind_vars] and [bind_patexprs], and
 * they're self-contained, so that they can be reused. In order to be as generic
 * as possible, they return a [substitution_kit], that is, a set of functions
 * that will substitute all bounds variables with the corresponding vars. *)
type substitution_kit = {
  (* substitute [TyBound]s for [TyOpen]s in a [typ]. *)
  subst_type: typ -> typ;
  (* substitute [TyBound]s for [TyOpen]s, [EVar]s for [EOpen]s in an [expression]. *)
  subst_expr: expression -> expression;
  (* substitute [TyBound]s for [TyOpen]s, [EVar]s for [EOpen]s in a [definitions]. *)
  subst_def: definitions -> definitions;
  (* substitute [PVar]s for [POpen]s in a pattern *)
  subst_pat: pattern list -> pattern list;
  (* the vars, in left-to-right order *)
  vars: var list;
}

(* [eunloc e] removes any [ELocated] located in front of [e]. *)
let rec eunloc = function
  | ELocated (e, _) ->
      eunloc e
  | _ as e ->
      e
;;



(* [bind_vars env bindings] adds [bindings] in the environment, and returns the
 * new environment, and a [substitution_kit]. It takes a list of bindings in
 * reading order. *)
let bind_evars (env: env) (bindings: type_binding list): env * substitution_kit =
  (* List kept in reverse, the usual trick *)
  let env, vars =
    List.fold_left (fun (env, vars) binding ->
      let env, var = bind_rigid env binding in
      env, var :: vars
    ) (env, []) bindings
  in
  let subst_type t =
    MzList.fold_lefti (fun i t var -> tsubst (TyOpen var) i t) t vars
  in
  let subst_expr t =
    MzList.fold_lefti (fun i t var ->
      let t = tsubst_expr (TyOpen var) i t in
      esubst (EOpen var) i t) t vars
  in
  let subst_def t =
    MzList.fold_lefti (fun i t var ->
      let t = tsubst_def (TyOpen var) i t in
      esubst_def (EOpen var) i t) t vars
  in
  (* Now keep the list in order. *)
  let vars = List.rev vars in
  let subst_pat patterns =
    let vars, patterns = List.fold_left (fun (vars, pats) pat ->
      let pat, vars = psubst pat vars in
      vars, pat :: pats
    ) (vars, []) patterns in
    assert (vars = []);
    let patterns = List.rev patterns in
    patterns
  in
  env, { subst_type; subst_expr; subst_def; subst_pat; vars = vars }
;;

let bind_vars (env: env) (bindings: SurfaceSyntax.type_binding list): env * substitution_kit =
  let bindings = List.map (fun (x, k, p) -> User (module_name env, x), k, p) bindings in
  bind_evars env bindings
;;


(* [bind_patexprs env rec_flag patexprs] takes a list of patterns and
 * expressions, whose recursivity depends on [rec_flag], collects the variables
 * in the patterns, binds them to new vars, and performs the correct
 * substitutions according to the recursivity flag. *)
let bind_patexprs env rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let names = List.map collect_pattern patterns in
  let names = List.flatten names in
  let bindings = List.map (fun (v, p) -> (v, KTerm, p)) names in
  (* TEMPORARY are the names important here, or just a hint? *)
  let env, kit = bind_vars env bindings in
  let expressions = match rec_flag with
    | Recursive ->
        let expressions = List.map kit.subst_expr expressions in
        expressions
    | Nonrecursive ->
        expressions
  in
  env, List.combine patterns expressions, kit
;;


module ExprPrinter = struct

  open MzPprint
  open TypePrinter

  let print_maybe_qualified_datacon dc =
    utf8string (SurfaceSyntax.print_maybe_qualified Datacon.print dc)
  ;;

  let pmaybe_qualified_datacon buf arg =
    pdoc buf ((fun () -> print_maybe_qualified_datacon arg), ())
  ;;


  let print_datacon_reference dref =
    print_maybe_qualified_datacon dref.SurfaceSyntax.datacon_unresolved
  ;;

  let rec print_patexpr env (pat, expr) =
    let type_annot, expr = match expr with
      | EConstraint (expr, t) ->
          colon ^^ space ^^ print_type env t, expr
      | _ ->
          empty, expr
    in
    print_pat env pat ^^ type_annot ^^ space ^^ equals ^^ jump (
      print_expr env expr
    )

  and print_patexprs env patexprs =
    separate_map (break 1 ^^ string "and" ^^ space) (print_patexpr env) patexprs

  and print_pat env = function
    | PVar (v, _) ->
        print_var env (User (module_name env, v))

    | POpen var ->
        print_var env (get_name env var)

    | PTuple pats ->
        lparen ^^
          separate (comma ^^ space) (List.map (print_pat env) pats) ^^
        rparen

    (* Foo { bar = bar; baz = baz; … } *)
    | PConstruct (dref, fieldnames) ->
        print_datacon (snd dref) ^^
          if List.length fieldnames > 0 then
            space ^^ lbrace ^^
            jump ~indent:4
              (separate_map
                (semi ^^ break 1)
                (fun (field, name) -> print_field_name field ^^ space ^^
                  equals ^^ space ^^ print_pat env name) fieldnames) ^^
            jump rbrace
          else
            empty

    | PAs (p1, p2) ->
        print_pat env p1 ^^ space ^^ string "as" ^^ space ^^ print_pat env p2

    | PAny ->
        underscore

  and print_tapp env = function
    | Named (x, t) ->
        let x = User (module_name env, x) in
        print_var env x ^^ space ^^ equals ^^ space ^^ print_type env t
    | Ordered t ->
        print_type env t

  and print_expr env = function
    | EConstraint (e, t) ->
        print_expr env e ^^ colon ^^ space ^^ print_type env t

    | EVar i ->
        string "EVar(" ^^ int i ^^ string ")"

    | EOpen var ->
        print_var env (get_name env var)

    | EBuiltin b ->
        string "builtin" ^^ space ^^ string b

    | ELet (rec_flag, patexprs, body) ->
        let env, patexprs, { subst_expr; _ } = bind_patexprs env rec_flag patexprs in
        let body = subst_expr body in
        string "let" ^^ print_rec_flag rec_flag ^^ space ^^
        print_patexprs env patexprs ^^ break 1 ^^ string "in" ^^ break 1 ^^
        print_expr env body

    | EBigLambdas (xs, e) ->
        let env, { subst_expr; _ } = bind_evars env (List.map fst xs) in
        let e = subst_expr e in
	brackets (
	  separate_map (comma ^^ space) (print_ebinder env) xs
	) ^^ space ^^
	print_expr env e

    (* fun [a] (x: τ): τ -> e *)
    | ELambda (arg, return_type, body) ->
        (* Bind the function argument. Its scope is [body] only, not the
           argument and return types. *)
        let env, { subst_expr; _ } = bind_evars env [ fresh_auto_name "arg", KTerm, location env ] in
        let x = subst_expr (EVar 0) in
        let body = subst_expr body in
        (* Print. *)
        string "lambda " ^^ jump (parens (
          print_expr env x ^^ colon ^^ space ^^
          print_type env arg
        )) ^^ colon ^^ space ^^ print_type env return_type ^^ space ^^ equals ^^
        jump (print_expr env body)

    | EAssign (e1, f, e2) ->
        print_expr env e1 ^^ dot ^^ print_field f ^^ space ^^ larrow ^^ jump (print_expr env e2)

    | EAssignTag (e1, d, _) ->
        tagof ^^ print_expr env e1 ^^ larrow ^^ print_datacon (snd d)
         (* d.previous_datacon is not printed *)

    | EAccess (e, f) ->
        print_expr env e ^^ dot ^^ print_field f

    | EApply (f, arg) ->
        let arg = print_expr env arg in
        let f = print_expr env f in
        f ^^ space ^^ arg

    | ETApply (f, arg, k) ->
        let arg = print_tapp env arg in
        let f = print_expr env f in
        f ^^ space ^^ lbracket ^^ arg ^^ space ^^ colon ^^ colon ^^ space ^^
        print_kind k ^^ rbracket

    | ETuple exprs ->
        let exprs = List.map (print_expr env) exprs in
        lparen ^^ separate (comma ^^ space) exprs ^^ rparen

    | EMatch (b, e, patexprs) ->
        let patexprs = List.map (fun (pat, expr) ->
          let vars = collect_pattern pat in
          let bindings = List.map (fun (v, p) -> (v, KTerm, p)) vars in
          let env, { subst_expr; _ } = bind_vars env bindings in
          let expr = subst_expr expr in
          print_pat env pat ^^ space ^^ arrow ^^ jump (print_expr env expr)
        ) patexprs in
        let explain = if b then string "explain" ^^ space else empty in
        string "match" ^^ space ^^ explain ^^ print_expr env e ^^ space ^^ string "with" ^^
        jump ~indent:0 (ifflat empty (bar ^^ space) ^^ separate (break 1 ^^ bar ^^ space) patexprs)


    | EConstruct (datacon, fieldexprs) ->
        let fieldexprs = List.map (fun (field, expr) ->
          print_field_name field ^^ space ^^ equals ^^ space ^^ print_expr env expr
        ) fieldexprs in
        let fieldexprs =
          if List.length fieldexprs > 0 then
            space ^^ lbrace ^^ jump (separate (semi ^^ break 1) fieldexprs) ^^ break 1 ^^ rbrace
          else
            empty
        in
        print_datacon (snd datacon) ^^ fieldexprs

    | EIfThenElse (b, e1, e2, e3) ->
        let explain = if b then string "explain" ^^ space else empty in
        string "if" ^^ space ^^ explain ^^ print_expr env e1 ^^ space ^^ string "then" ^^
        jump (print_expr env e2) ^^ break 1 ^^ string "else" ^^
        jump (print_expr env e3)

    | ELocated (e, _) ->
        print_expr env e

    | EInt i ->
        int i

    | EExplained e ->
        print_expr env e ^^ space ^^ string "explained"

    | EGive (e1, e2) ->
        string "give" ^^ space ^^ print_expr env e1 ^^ space ^^
        string "to" ^^ space ^^ print_expr env e2

    | ETake (e1, e2) ->
        string "take" ^^ space ^^ print_expr env e1 ^^ space ^^
        string "from" ^^ space ^^ print_expr env e2

    | EOwns (e1, e2) ->
        print_expr env e1 ^^ space ^^
        string "owns" ^^ space ^^
       print_expr env e2

    | EFail ->
        string "fail"

  and print_rec_flag = function
    | Recursive ->
        string " rec"
    | Nonrecursive ->
        empty


  and print_ebinder env ((name, kind, _), f) =
    let f = if f = AutoIntroduced then star else empty in
    print_var env name ^^ f ^^ space ^^ colon ^^ space ^^ print_kind kind

  and print_binder env (((name: Variable.name), kind, pos), f) =
    print_ebinder env ((User (module_name env, name), kind, pos), f)
  ;;

  let print_definitions env (_loc, rec_flag, patexprs) =
    let env, patexprs, _ = bind_patexprs env rec_flag patexprs in
    string "val" ^^ print_rec_flag rec_flag ^^ space ^^ print_patexprs env patexprs
  ;;

  let print_sig_item env (x, t) =
    print_var env (User (module_name env, x)) ^^ space ^^ at ^^ space ^^ print_type env t
  ;;

  let psigitem buf (env, arg) =
    pdoc buf ((fun () -> print_sig_item env arg), ())
  ;;

  let pdefinitions buf arg =
    pdoc buf ((fun (env, declarations) -> print_definitions env declarations), arg)
  ;;

  let pexpr buf arg =
    pdoc buf ((fun (env, expr) -> print_expr env expr), arg)
  ;;

  let ppat buf arg =
    pdoc buf ((fun (env, pat) -> print_pat env pat), arg)
  ;;

end
