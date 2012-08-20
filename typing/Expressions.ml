(* This file contains our internal syntax for expressions. *)

open Types
open Flexible

(* ---------------------------------------------------------------------------- *)

(* Patterns *)

(* The De Bruijn numbering is defined according to a depth-first traversal of
 * the pattern: the first variable encountered will have index 0, and so on. *)
type pattern =
  (* x *)
  | PVar of Variable.name * (Lexing.position * Lexing.position)
  (* (x₁, …, xₙ) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of Datacon.name * (Field.name * pattern) list
  (* Once the variables in a pattern have been bound, they may replaced by
   * [PPoint]s so that we know how to speak about the bound variables. *)
  | PPoint of point

(* ---------------------------------------------------------------------------- *)

(* Expressions *)

type rec_flag = SurfaceSyntax.rec_flag = Nonrecursive | Recursive

type expression =
  (* e: τ *)
  | EConstraint of expression * typ
  (* v, bound *)
  | EVar of index
  (* v, free *)
  | EPoint of point
  (* let rec pat = expr and pat' = expr' in expr *)
  | ELet of rec_flag * patexpr list * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of type_binding list * typ * typ * expression
  (* v.f <- e *)
  | EAssign of expression * Field.name * expression
  (* v <- Foo *)
  | EAssignTag of expression * Datacon.name
  (* v.f *)
  | EAccess of expression * Field.name
  (* e₁ e₂ *)
  | EApply of expression * expression
  (* match e with pᵢ -> eᵢ *)
  | EMatch of bool * expression * patexpr list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of Datacon.name * (Field.name * expression) list
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of bool * expression * expression * expression
  | ELocated of expression * Lexing.position * Lexing.position
  | EInt of int
  (* Explanations *)
  | EExplained of expression
  (* fail *)
  | EFail

and patexpr =
  (* A binding is made up of a pattern, an optional type annotation for the
   * entire pattern (desugared), and an expression. *)
  pattern * expression


(* The grammar below doesn't enforce the “only variables are allowed on the
 * left-hand side of a let rec” rule. We'll see to that later. Here too, the
 * order of the bindings is significant: if the binding is recursive, the
 * variables in all the patterns are collected in order before type-checking the
 * expressions. *)
type declaration =
  | DMultiple of rec_flag * patexpr list
  | DLocated of declaration * Lexing.position * Lexing.position

type declaration_group =
  declaration list

let e_unit =
  ETuple []
;;

let p_unit =
  PTuple []
;;

let e_assert perm expr =
  ELet (
    Nonrecursive,
    [p_unit,
    EConstraint (e_unit, TyBar (ty_unit, perm))],
    expr
  )
;;

(* ---------------------------------------------------------------------------- *)

(* Moar fun with De Bruijn. *)

(* [collect_pattern] returns the list of bindings present in the pattern. The
 * binding with index [i] in the returned list has De Bruijn index [i] in the
 * bound term. *)
let collect_pattern (p: pattern): ((Types.name * (Lexing.position * Lexing.position)) list) =
  let rec collect_pattern acc = function
  | PVar (name, p) ->
      (User name, p) :: acc
  | PTuple patterns ->
      List.fold_left collect_pattern acc patterns
  | PConstruct (_, fields) ->
      let patterns = snd (List.split fields) in
      List.fold_left collect_pattern acc patterns
  | PPoint _ ->
      assert false
  in
  (* Return the names in reading order, i.e. left-to-right. *)
  List.rev (collect_pattern [] p)
;;

(* [psubst pat points] replaces names in [pat] as it goes, by popping points off
 * the front of [points]. *)
let rec psubst (pat: pattern) (points: point list) =
  match pat with
  | PVar _ ->
      begin match points with
      | hd :: tl ->
          PPoint hd, tl
      | _ ->
          Log.error "Wrong variable count for [psubst]"
      end

  | PPoint _ ->
      Log.error "You ran a pattern through [psubst] twice"

  | PTuple pats ->
      let pats, points = List.fold_left (fun (pats, points) pat ->
          let pat, points = psubst pat points in
          pat :: pats, points
        ) ([], points) pats
      in
      let pats = List.rev pats in
      PTuple pats, points

  | PConstruct (datacon, fieldpats) ->
      let fieldpats, points = List.fold_left (fun (fieldpats, points) (field, pat) ->
          let pat, points = psubst pat points in
          (field, pat) :: fieldpats, points
        ) ([], points) fieldpats
      in
      let fieldpats = List.rev fieldpats in
      PConstruct (datacon, fieldpats), points
;;


let rec tsubst_patexprs t2 i rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let names = List.fold_left (fun acc p ->
    collect_pattern p :: acc) [] patterns
  in
  let names = List.flatten names in
  let n = List.length names in
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
  | EPoint _ ->
      e

  | ELet (rec_flag, patexprs, body) ->
      let n, patexprs = tsubst_patexprs t2 i rec_flag patexprs in
      let body = tsubst_expr t2 (i + n) body in
      ELet (rec_flag, patexprs, body)

  | EFun (vars, arg, return_type, body) ->
      let i = i + List.length vars in
      let arg = tsubst t2 i arg in
      let return_type = tsubst t2 i return_type in
      let body = tsubst_expr t2 i body in
      EFun (vars, arg, return_type, body)

  | EAssign (e1, field, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EAssign (e1, field, e2)

  | EAssignTag (e1, datacon) ->
      let e1 = tsubst_expr t2 i e1 in
      EAssignTag (e1, datacon)

  | EAccess (e1, field) ->
      let e1 = tsubst_expr t2 i e1 in
      EAccess (e1, field)

  | EApply (f, arg) ->
      let f = tsubst_expr t2 i f in
      let arg = tsubst_expr t2 i arg in
      EApply (f, arg)

  | EMatch (b, e, patexprs) ->
      let e = tsubst_expr t2 i e in
      let patexprs = List.map (fun (pat, expr) ->
          let names = collect_pattern pat in
          let n = List.length names in
          pat, tsubst_expr t2 (i + n) expr
        ) patexprs
      in
      EMatch (b, e, patexprs)

  | ETuple exprs ->
      let exprs = List.map (tsubst_expr t2 i) exprs in
      ETuple exprs

  | EConstruct (name, fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, tsubst_expr t2 i expr) fieldexprs
      in
      EConstruct (name, fieldexprs)

  | EIfThenElse (b, e1, e2, e3) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      let e3 = tsubst_expr t2 i e3 in
      EIfThenElse (b, e1, e2, e3)

  | ELocated (e, p1, p2) ->
      let e = tsubst_expr t2 i e in
      ELocated (e, p1, p2)

  | EInt _ ->
      e

  | EExplained e ->
      let e = tsubst_expr t2 i e in
      EExplained e

  | EFail ->
      EFail


(* [tsubst_decl t2 i decls] substitutes type [t2] for index [i] in a list of
 * declarations [decls]. *)
and tsubst_decl e2 i decls =
  let rec tsubst_decl acc i = function
    | DLocated (DMultiple (rec_flag, patexprs), p1, p2) :: decls ->
        let n, patexprs = tsubst_patexprs e2 i rec_flag patexprs in
        tsubst_decl (DLocated (DMultiple (rec_flag, patexprs), p1, p2) :: acc) (i + n) decls
    | [] ->
        List.rev acc
    | _ ->
        assert false
  in
  tsubst_decl [] i decls
;;

let rec esubst_patexprs e2 i rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let names = List.fold_left (fun acc p ->
    collect_pattern p :: acc) [] patterns
  in
  let names = List.flatten names in
  let n = List.length names in
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

  | EPoint _ ->
      e1

  | ELet (rec_flag, patexprs, body) ->
      let n, patexprs = esubst_patexprs e2 i rec_flag patexprs in
      let body = esubst e2 (i + n) body in
      ELet (rec_flag, patexprs, body)

  | EFun (vars, arg, return_type, body) ->
      let n = List.length vars in
      let body = esubst e2 (i + n) body in
      EFun (vars, arg, return_type, body)

  | EAssign (e, f, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EAssign (e, f, e')

  | EAssignTag (e, d) ->
      let e = esubst e2 i e in
      EAssignTag (e, d)

  | EAccess (e, f) ->
      let e = esubst e2 i e in
      EAccess (e, f)

  | EApply (f, arg) ->
      let f = esubst e2 i f in
      let arg = esubst e2 i arg in
      EApply (f, arg)

  | EMatch (b, e, patexprs) ->
      let e = esubst e2 i e in
      let patexprs = List.map (fun (pat, expr) ->
        let names = collect_pattern pat in
        let n = List.length names in
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


  | ELocated (e, p1, p2) ->
      let e = esubst e2 i e in
      ELocated (e, p1, p2)

  | EInt _ ->
      e1

  | EExplained e ->
      let e = esubst e2 i e in
      EExplained e

  | EFail ->
      EFail

(* [esubst_decl e2 i decls] substitutes expression [e2] for index [i] in a list of
 * declarations [decls]. *)
and esubst_decl e2 i decls =
  let rec esubst_decl acc i = function
    | DLocated (DMultiple (rec_flag, patexprs), p1, p2) :: decls ->
        let n, patexprs = esubst_patexprs e2 i rec_flag patexprs in
        esubst_decl (DLocated (DMultiple (rec_flag, patexprs), p1, p2) :: acc) (i + n) decls
    | [] ->
        List.rev acc
    | _ ->
        assert false
  in
  esubst_decl [] i decls
;;


(* The idea is that when you bind, say, a list of variables, either PERM, TYPE
 * or TERM, (through type bindings, or a pattern in a let-binding), you want to
 * perform the substitutions on whatever's under the bound variables. The
 * functions that perform the binding are [bind_vars] and [bind_patexprs], and
 * they're self-contained, so that they can be reused. In order to be as generic
 * as possible, they return a [substitution_kit], that is, a set of functions
 * that will substitute all bounds variables with the corresponding points. *)
type substitution_kit = {
  (* substitute [TyVar]s for [TyPoint]s in a [typ]. *)
  subst_type: typ -> typ;
  (* substitute [TyVar]s for [TyPoint]s, [EVar]s for [EPoint]s in an [expression]. *)
  subst_expr: expression -> expression;
  (* substitute [TyVar]s for [TyPoint]s, [EVar]s for [EPoint]s in an [expression]. *)
  subst_decl: declaration list -> declaration list;
  (* substitute [PVar]s for [PPoint]s in a pattern *)
  subst_pat: pattern list -> pattern list;
  (* the points, in left-to-right order *)
  points: point list;
}

(* [eunloc e] removes any [ELocated] located in front of [e]. *)
let rec eunloc = function
  | ELocated (e, _, _) ->
      eunloc e
  | _ as e ->
      e
;;


let eloc = function
  | ELocated (_, p1, p2) ->
      p1, p2
  | _ ->
      Log.error "Only call this function when you're sure there's a ELocated node."
;;


(* [bind_vars env bindings] adds [bindings] in the environment, and returns the
 * new environment, and a [substitution_kit]. It takes a list of bindings in
 * reading order. *)
let bind_vars (env: env) (bindings: type_binding list): env * substitution_kit =
  (* List kept in reverse, the usual trick *)
  let env, points =
    List.fold_left (fun (env, points) binding ->
      let env, point = bind_var env binding in
      env, point :: points
    ) (env, []) bindings
  in
  let subst_type t =
    Hml_List.fold_lefti (fun i t point -> tsubst (TyPoint point) i t) t points
  in
  let subst_expr t =
    Hml_List.fold_lefti (fun i t point ->
      let t = tsubst_expr (TyPoint point) i t in
      esubst (EPoint point) i t) t points
  in
  let subst_decl t =
    Hml_List.fold_lefti (fun i t point ->
      let t = tsubst_decl (TyPoint point) i t in
      esubst_decl (EPoint point) i t) t points
  in
  (* Now keep the list in order. *)
  let points = List.rev points in
  let subst_pat patterns =
    let points, patterns = List.fold_left (fun (points, pats) pat ->
      let pat, points = psubst pat points in
      points, pat :: pats
    ) (points, []) patterns in
    assert (points = []);
    let patterns = List.rev patterns in
    patterns
  in
  env, { subst_type; subst_expr; subst_decl; subst_pat; points = points }
;;


(* [bind_patexprs env rec_flag patexprs] takes a list of patterns and
 * expressions, whose recursivity depends on [rec_flag], collects the variables
 * in the patterns, binds them to new points, and performs the correct
 * substitutions according to the recursivity flag. *)
let bind_patexprs env rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let names = List.map collect_pattern patterns in
  let names = List.flatten names in
  let bindings = List.map (fun (v, p) -> (v, KTerm, p)) names in
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


let elift (k: int) (e: expression) =
  let rec elift (i: int) (e: expression) =
  match e with
  | EConstraint (e, t) ->
      EConstraint (elift i e, lift i t)

  | EVar j ->
      if j < i then
        EVar j
      else
        EVar (j + k)

  | EPoint _ ->
      e

  | ELet (flag, patexprs, body) ->
      let patterns, expressions = List.split patexprs in
      let names = List.map collect_pattern patterns in
      let n = List.length (List.flatten names) in
      let expressions = match flag with
        | Recursive ->
            List.map (elift (i + n)) expressions
        | Nonrecursive ->
            List.map (elift i) expressions
      in
      let patexprs = List.combine patterns expressions in
      let body = elift (i + n) body in
      ELet (flag, patexprs, body)


  | EFun (vars, arg, return_type, body) ->
      let n = List.length vars in
      let arg = lift (i + n) arg in
      let return_type = lift (i + n) return_type in
      let body = elift (i + n) body in
      EFun (vars, arg, return_type, body)


  | EAssign (e1, f, e2) ->
      EAssign (elift i e1, f, elift i e2)

  | EAssignTag (e1, d) ->
      EAssignTag (elift i e1, d)

  | EAccess (e, f) ->
      EAccess (elift i e, f)

  | EApply (e1, e2) ->
      EApply (elift i e1, elift i e2)

  | EMatch (b, e, patexprs) ->
      let e = elift i e in
      let patexprs = List.map (fun (pat, expr) ->
        let n = List.length (collect_pattern pat) in
        pat, elift (i + n) expr
      ) patexprs in
      EMatch (b, e, patexprs)

  | ETuple es ->
      ETuple (List.map (elift i) es)

  | EConstruct (datacon, fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, elift i expr
      ) fieldexprs in
      EConstruct (datacon, fieldexprs)

  | EIfThenElse (b, e1, e2, e3) ->
      EIfThenElse (b, elift i e1, elift i e2, elift i e3)

  | ELocated (e, p1, p2) ->
      ELocated (elift i e, p1, p2)

  | EInt _ ->
      e

  | EExplained e ->
      EExplained (elift i e)

  | EFail ->
      EFail
  in
  elift 0 e

;;


let epsubst (env: env) (e2: expression) (p: point) (e1: expression): expression =
  let rec epsubst e2 e1 =
    match e1 with
    | EConstraint (e1, t) ->
        EConstraint (epsubst e2 e1, t)

    | EVar _ ->
        e1

    | EPoint p' ->
        if same env p p' then
          e2
        else
          e1

    | ELet (flag, patexprs, body) ->
        let patterns, expressions = List.split patexprs in
        let names = List.map collect_pattern patterns in
        let n = List.length (List.flatten names) in
        let expressions = match flag with
          | Recursive ->
              let e2 = elift n e2 in
              List.map (epsubst e2) expressions
          | Nonrecursive ->
              List.map (epsubst e2) expressions
        in
        let patexprs = List.combine patterns expressions in
        let e2 = elift n e2 in
        let body = epsubst e2 body in
        ELet (flag, patexprs, body)


    | EFun (vars, arg, return_type, body) ->
        let n = List.length vars in
        let e2 = elift n e2 in
        let body = epsubst e2 body in
        EFun (vars, arg, return_type, body)

    | EAssign (e1, f, e'1) ->
        EAssign (epsubst e2 e1, f, epsubst e2 e'1)

    | EAssignTag (e1, d) ->
        EAssignTag (epsubst e2 e1, d)

    | EAccess (e1, f) ->
        EAccess (epsubst e2 e1, f)

    | EApply (e1, e'1) ->
        EApply (epsubst e2 e1, epsubst e2 e'1)

    | EMatch (b, e1, patexprs) ->
        let e1 = epsubst e2 e1 in
        let patexprs = List.map (fun (pat, expr) ->
          let n = List.length (collect_pattern pat) in
          let e2 = elift n e2 in
          pat, epsubst e2 expr
        ) patexprs in
        EMatch (b, e1, patexprs)


    | ETuple es ->
        ETuple (List.map (epsubst e2) es)

    | EConstruct (datacon, fieldexprs) ->
        let fieldexprs = List.map (fun (field, expr) ->
          field, epsubst e2 expr
        ) fieldexprs in
        EConstruct (datacon, fieldexprs)

    | EIfThenElse (b, e1, e1', e1'') ->
        EIfThenElse (b, epsubst e2 e1, epsubst e2 e1', epsubst e2 e1'')

    | ELocated (e, p1, p2) ->
        ELocated (epsubst e2 e, p1, p2)

    | EInt _ ->
        e1

    | EExplained e ->
        EExplained (epsubst e2 e)

    | EFail ->
        EFail
  in

  epsubst e2 e1
;;

let tepsubst (env: env) (t2: typ) (p: point) (e1: expression): expression =
  let rec tepsubst t2 e1 =
    match e1 with
    | EConstraint (e1, t) ->
        EConstraint (tepsubst t2 e1, tpsubst env t2 p t)

    | EVar _ ->
        e1

    | EPoint _ ->
        e1

    | ELet (flag, patexprs, body) ->
        let patterns, expressions = List.split patexprs in
        let names = List.map collect_pattern patterns in
        let n = List.length (List.flatten names) in
        let expressions = match flag with
          | Recursive ->
              let t2 = lift n t2 in
              List.map (tepsubst t2) expressions
          | Nonrecursive ->
              List.map (tepsubst t2) expressions
        in
        let patexprs = List.combine patterns expressions in
        let t2 = lift n t2 in
        let body = tepsubst t2 body in
        ELet (flag, patexprs, body)


    | EFun (vars, arg, return_type, body) ->
        let n = List.length vars in
        let t2 = lift n t2 in
        let body = tepsubst t2 body in
        let arg = tpsubst env t2 p arg in
        let return_type = tpsubst env t2 p return_type in
        EFun (vars, arg, return_type, body)

    | EAssign (e1, f, e'1) ->
        EAssign (tepsubst t2 e1, f, tepsubst t2 e'1)

    | EAssignTag (e1, d) ->
        EAssignTag (tepsubst t2 e1, d)

    | EAccess (e1, f) ->
        EAccess (tepsubst t2 e1, f)

    | EApply (e1, e'1) ->
        EApply (tepsubst t2 e1, tepsubst t2 e'1)

    | EMatch (b, e1, patexprs) ->
        let e1 = tepsubst t2 e1 in
        let patexprs = List.map (fun (pat, expr) ->
          let n = List.length (collect_pattern pat) in
          let t2 = lift n t2 in
          pat, tepsubst t2 expr
        ) patexprs in
        EMatch (b, e1, patexprs)


    | ETuple es ->
        ETuple (List.map (tepsubst t2) es)

    | EConstruct (datacon, fieldexprs) ->
        let fieldexprs = List.map (fun (field, expr) ->
          field, tepsubst t2 expr
        ) fieldexprs in
        EConstruct (datacon, fieldexprs)

    | EIfThenElse (b, e1, e1', e1'') ->
        EIfThenElse (b, tepsubst t2 e1, tepsubst t2 e1', tepsubst t2 e1'')

    | ELocated (e, p1, p2) ->
        ELocated (tepsubst t2 e, p1, p2)

    | EInt _ ->
        e1

    | EExplained e ->
        EExplained (tepsubst t2 e)

    | EFail ->
        EFail
  in

  tepsubst t2 e1
;;


module ExprPrinter = struct

  open Hml_Pprint
  open TypePrinter

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
    join (break1 ^^ string "and" ^^ space) (List.map (print_patexpr env) patexprs)

  and print_pat env = function
    | PVar (v, _) ->
        print_var (User v)

    | PPoint point ->
        print_var (get_name env point)

    | PTuple pats ->
        lparen ^^
          join (comma ^^ space) (List.map (print_pat env) pats) ^^
        rparen

    (* Foo { bar = bar; baz = baz; … } *)
    | PConstruct (name, fieldnames) ->
        print_datacon name ^^
          if List.length fieldnames > 0 then
            space ^^ lbrace ^^
            jump ~indent:4
              (join
                (semi ^^ break1)
                (List.map (fun (field, name) -> print_field field ^^ space ^^
                  equals ^^ space ^^ print_pat env name) fieldnames)) ^^
            jump rbrace
          else
            empty

  and print_expr env = function
    | EConstraint (e, t) ->
        print_expr env e ^^ colon ^^ space ^^ print_type env t

    | EVar i ->
        int i

    | EPoint point ->
        print_var (get_name env point)

    | ELet (rec_flag, patexprs, body) ->
        let env, patexprs, { subst_expr; _ } = bind_patexprs env rec_flag patexprs in
        let body = subst_expr body in
        string "let" ^^ print_rec_flag rec_flag ^^ space ^^
        print_patexprs env patexprs ^^ break1 ^^ string "in" ^^ break1 ^^
        print_expr env body

    (* fun [a] (x: τ): τ -> e *)
    | EFun (vars, arg, return_type, body) ->
        let env, { subst_type; subst_expr; _ } = bind_vars env vars in
        (* Remember: this is all in desugared form, so the variables in [args]
         * are all bound. *)
        let arg = subst_type arg in
        let return_type = subst_type return_type in
        let body = subst_expr body in
        string "fun " ^^ lbracket ^^ join (comma ^^ space) (List.map print_binder vars) ^^
        rbracket ^^ jump (
          print_type env arg
        ) ^^ colon ^^ space ^^ print_type env return_type ^^ space ^^ equals ^^
        jump (print_expr env body)

    | EAssign (e1, f, e2) ->
        print_expr env e1 ^^ dot ^^ print_field f ^^ space ^^ larrow ^^ jump (print_expr env e2)

    | EAssignTag (e1, d) ->
        print_expr env e1 ^^ dot ^^ print_datacon d ^^ space ^^ langle ^^ equals ^^
        print_datacon d

    | EAccess (e, f) ->
        print_expr env e ^^ dot ^^ print_field f

    | EApply (f, arg) ->
        let arg = print_expr env arg in
        let f = print_expr env f in
        f ^^ space ^^ arg

    | ETuple exprs ->
        let exprs = List.map (print_expr env) exprs in
        lparen ^^ join (comma ^^ space) exprs ^^ rparen

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
        jump ~indent:0 (ifflat empty (bar ^^ space) ^^ join (break1 ^^ bar ^^ space) patexprs)


    | EConstruct (datacon, fieldexprs) ->
        let fieldexprs = List.map (fun (field, expr) ->
          print_field field ^^ space ^^ equals ^^ space ^^ print_expr env expr
        ) fieldexprs in
        let fieldexprs =
          if List.length fieldexprs > 0 then
            space ^^ lbrace ^^ jump (join (semi ^^ break1) fieldexprs) ^^ break1 ^^ rbrace
          else
            empty
        in
        print_datacon datacon ^^ fieldexprs

    | EIfThenElse (b, e1, e2, e3) ->
        let explain = if b then string "explain" ^^ space else empty in
        string "if" ^^ space ^^ explain ^^ print_expr env e1 ^^ space ^^ string "then" ^^
        jump (print_expr env e2) ^^ break1 ^^ string "else" ^^
        jump (print_expr env e3)

    | ELocated (e, _, _) ->
        print_expr env e

    | EInt i ->
        int i

    | EExplained e ->
        print_expr env e ^^ space ^^ string "explained"

    | EFail ->
        string "fail"

  and print_rec_flag = function
    | Recursive ->
        string " rec"
    | Nonrecursive ->
        empty


  and print_binder (name, kind, _) =
    print_var name ^^ space ^^ ccolon ^^ space ^^ print_kind kind

  ;;

  let rec print_declaration env declaration: env * document * _  =
    match declaration with
    | DLocated (declaration, _, _) ->
        print_declaration env declaration
    | DMultiple (rec_flag, patexprs) ->
        let env, patexprs, { subst_decl; _ } = bind_patexprs env rec_flag patexprs in
        env,
        string "val" ^^ print_rec_flag rec_flag ^^ space ^^ print_patexprs env patexprs,
        subst_decl
  ;;

  let print_declarations env declarations =
    let rec print_declarations env acc declarations =
      match declarations with
      | declaration :: declarations ->
          let env, doc, subst_decl = print_declaration env declaration in
          let declarations = subst_decl declarations in
          print_declarations env (doc :: acc) declarations
      | [] ->
          List.rev acc
    in
    let declarations = print_declarations env [] declarations in
    let declarations = hardline ^^ join (hardline ^^ hardline) declarations in
    colors.red ^^ string "DECLARATIONS:" ^^ colors.default ^^
    nest 2 declarations ^^ hardline
  ;;

  let pdeclarations buf arg =
    pdoc buf ((fun (env, declarations) -> print_declarations env declarations), arg)
  ;;

  let pexpr buf arg =
    pdoc buf ((fun (env, expr) -> print_expr env expr), arg)
  ;;

  let ppat buf arg =
    pdoc buf ((fun (env, pat) -> print_pat env pat), arg)
  ;;

end
