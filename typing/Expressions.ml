(* This file contains our internal syntax for expressions. *)

open Types

(* ---------------------------------------------------------------------------- *)

(* Patterns *)

(* The De Bruijn numbering is defined according to a depth-first traversal of
 * the pattern: the first variable encountered will have index 0, and so on. *)
type pattern =
  (* x: τ *)
  | PConstraint of pattern * typ
  (* x *)
  | PVar of Variable.name
  (* Once the variables in a pattern have been bound, they may replaced by
   * [PPoint]s so that we know how to speak about the bound variables. *)
  | PPoint of point
  (* (x₁, …, xₙ) *)
  | PTuple of pattern list
  (* Foo { bar = bar; baz = baz; … } *)
  | PConstruct of Datacon.name * (Field.name * pattern) list
  | PLocated of pattern * Lexing.position * Lexing.position

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
  | ELet of rec_flag * (pattern * expression) list * expression
  (* fun [a] (x: τ): τ -> e *)
  | EFun of (Variable.name * kind) list * typ list * typ * expression
  (* v.f <- e *)
  | EAssign of expression * Field.name * expression
  (* v.f *)
  | EAccess of expression * Field.name
  (* e₁ e₂ *)
  | EApply of expression * expression
  (* match e with pᵢ -> eᵢ *)
  | EMatch of expression * (pattern * expression) list
  (* (e₁, …, eₙ) *)
  | ETuple of expression list
  (* Foo { bar = bar; baz = baz; … *)
  | EConstruct of Datacon.name * (Field.name * expression) list
  (* if e₁ then e₂ else e₃ *)
  | EIfThenElse of expression * expression * expression
  | ELocated of expression * Lexing.position * Lexing.position
  (* Arithmetic *)
  | EPlus of expression * expression
  | EMinus of expression * expression
  | ETimes of expression * expression
  | EDiv of expression * expression
  | EUMinus of expression
  | EInt of int


(* The grammar below doesn't enforce the “only variables are allowed on the
 * left-hand side of a let rec” rule. We'll see to that later. Here too, the
 * order of the bindings is significant: if the binding is recursive, the
 * variables in all the patterns are collected in order before type-checking the
 * expressions. *)
type declaration =
  | DMultiple of rec_flag * (pattern * expression) list
  | DLocated of declaration * Lexing.position * Lexing.position

type declaration_group =
  declaration list

(* ---------------------------------------------------------------------------- *)

(* Moar fun with De Bruijn. *)

(* [collect_pattern] returns the list of bindings present in the pattern. The
 * binding with index [i] in the returned list has De Bruijn index [i] in the
 * bound term. *)
let collect_pattern p =
  let rec collect_pattern acc = function
  | PConstraint (p, _) ->
      collect_pattern acc p
  | PVar name ->
      name :: acc
  | PTuple patterns ->
      List.fold_left collect_pattern acc patterns
  | PConstruct (_, fields) ->
      let patterns = snd (List.split fields) in
      List.fold_left collect_pattern acc patterns
  | PLocated (p, _, _) ->
      collect_pattern acc p
  | PPoint _ ->
      assert false
  in
  List.rev (collect_pattern [] p)
;;

(* [psubst pat points] replaces names in [pat] as it goes, by popping points off
 * the front of [points]. *)
let rec psubst (pat: pattern) (points: point list) =
  match pat with
  | PConstraint (p, t) ->
      let p, points = psubst p points in
      PConstraint (p, t), points

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

  | PConstruct _ ->
      pat, points

  | PLocated (pat, p1, p2) ->
      let pat, points = psubst pat points in
      PLocated (pat, p1, p2), points
;;


(* [tsubst_pat t2 i p] replaces all occurrences of [TyVar i] with [t2] in
 * pattern [p]. *)
let rec tsubst_pat t2 i p =
  match p with
  | PConstraint (p, t) ->
      let p = tsubst_pat t2 i p in
      let t = tsubst t2 i t in
      PConstraint (p, t)

  | PVar _
  | PPoint _
  | PConstruct _ ->
      p

  | PTuple p ->
      let p = List.map (tsubst_pat t2 i) p in
      PTuple p

  | PLocated (p, p1, p2) ->
      let p = tsubst_pat t2 i p in
      PLocated (p, p1, p2)
;;


let rec tsubst_patexprs t2 i rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let patterns = List.map (tsubst_pat t2 i) patterns in
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

  | EFun (vars, args, return_type, body) ->
      let i = i + List.length vars in
      let args = List.map (tsubst t2 i) args in
      let return_type = tsubst t2 i return_type in
      let body = tsubst_expr t2 i body in
      EFun (vars, args, return_type, body)

  | EAssign (e1, field, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EAssign (e1, field, e2)

  | EAccess (e1, field) ->
      let e1 = tsubst_expr t2 i e1 in
      EAccess (e1, field)

  | EApply (f, arg) ->
      let f = tsubst_expr t2 i f in
      let arg = tsubst_expr t2 i arg in
      EApply (f, arg)

  | EMatch (e, patexprs) ->
      let e = tsubst_expr t2 i e in
      let patexprs = List.map (fun (pat, expr) ->
          let pat = tsubst_pat t2 i pat in
          let names = collect_pattern pat in
          let n = List.length names in
          pat, tsubst_expr t2 (i + n) expr
        ) patexprs
      in
      EMatch (e, patexprs)

  | ETuple exprs ->
      let exprs = List.map (tsubst_expr t2 i) exprs in
      ETuple exprs

  | EConstruct (name, fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, tsubst_expr t2 i expr) fieldexprs
      in
      EConstruct (name, fieldexprs)

  | EIfThenElse (e1, e2, e3) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      let e3 = tsubst_expr t2 i e3 in
      EIfThenElse (e1, e2, e3)

  | ELocated (e, p1, p2) ->
      let e = tsubst_expr t2 i e in
      ELocated (e, p1, p2)

  | EPlus (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EPlus (e1, e2)

  | EMinus (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EMinus (e1, e2)

  | ETimes (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      ETimes (e1, e2)

  | EDiv (e1, e2) ->
      let e1 = tsubst_expr t2 i e1 in
      let e2 = tsubst_expr t2 i e2 in
      EDiv (e1, e2)

  | EUMinus e ->
      let e = tsubst_expr t2 i e in
      EUMinus e

  | EInt _ ->
      e


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

  | EFun (vars, params, return_type, body) ->
      let n = List.length vars in
      let body = esubst e2 (i + n) body in
      EFun (vars, params, return_type, body)

  | EAssign (e, f, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EAssign (e, f, e')

  | EAccess (e, f) ->
      let e = esubst e2 i e in
      EAccess (e, f)

  | EApply (f, arg) ->
      let f = esubst e2 i f in
      let arg = esubst e2 i arg in
      EApply (f, arg)

  | EMatch (e, patexprs) ->
      let e = esubst e2 i e in
      let patexprs = List.map (fun (pat, expr) ->
        let names = collect_pattern pat in
        let n = List.length names in
        let expr = esubst e2 (i + n) expr in
        pat, expr) patexprs
      in
      EMatch (e, patexprs)

  | ETuple exprs ->
      let exprs = List.map (esubst e2 i) exprs in
      ETuple exprs

  | EConstruct (name, fieldexprs) ->
      let fieldexprs = List.map (fun (field, expr) ->
        field, esubst e2 i expr) fieldexprs
      in
      EConstruct (name, fieldexprs)

  | EIfThenElse (e, e', e'') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      let e'' = esubst e2 i e'' in
      EIfThenElse (e, e', e'')


  | ELocated (e, p1, p2) ->
      let e = esubst e2 i e in
      ELocated (e, p1, p2)

  | EPlus (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EPlus (e, e')

  | EMinus (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EMinus (e, e')

  | ETimes (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      ETimes (e, e')

  | EDiv (e, e') ->
      let e = esubst e2 i e in
      let e' = esubst e2 i e' in
      EDiv (e, e')

  | EUMinus e ->
      let e = esubst e2 i e in
      EUMinus e

  | EInt _ ->
      e1

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
  subst_pat: pattern -> pattern;
}

(* [eunloc e] removes any [ELocated] located in front of [e]. *)
let eunloc = function
  | ELocated (e, _, _)
  | (_ as e) ->
      e
;;

(* [punloc p] removes any [PLocated] located in front of [p]. *)
let punloc = function
  | PLocated (p, _, _)
  | (_ as p) ->
      p
;;


(* [bind_vars env bindings] adds [bindings] in the environment, and returns the
 * new environment, and a [substitution_kit]. *)
let bind_vars (env: env) (bindings: type_binding list): env * substitution_kit =
  (* List kept in reverse, the usual trick *)
  let env, points = List.fold_left (fun (env, points) binding ->
    let env, point = bind_var env binding in
    env, point :: points) (env, []) bindings
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
  let subst_pat p =
    let pat, points = psubst p points in
    assert (points = []);
    pat
  in
  env, { subst_type; subst_expr; subst_decl; subst_pat }
;;


(* [bind_patexprs env rec_flag patexprs] takes a list of patterns and
 * expressions, whose recursivity depends on [rec_flag], collects the variables
 * in the patterns, binds them to new points, and performs the correct
 * substitutions according to the recursivity flag. *)
let bind_patexprs env rec_flag patexprs =
  let patterns, expressions = List.split patexprs in
  let names = List.fold_left (fun acc p ->
    collect_pattern p :: acc) [] patterns
  in
  let names = List.rev names in
  let names = List.flatten names in
  let bindings = List.map (fun n -> (n, KTerm)) names in
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

  open Hml_Pprint
  open TypePrinter

  let rec print_patexpr env (pat, expr) =
    print_pat env pat ^^ space ^^ equals ^^ jump (
      print_expr env expr
    )

  and print_patexprs env patexprs =
    join (break1 ^^ string "and" ^^ space) (List.map (print_patexpr env) patexprs)

  and print_pat env = function
    | PConstraint (p, t) ->
        print_pat env p ^^ colon ^^ space ^^ print_type env t

    | PVar v ->
        print_var v

    | PPoint _ ->
        assert false

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

    | PLocated (pat, _, _) ->
        print_pat env pat

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
    | EFun (vars, args, return_type, body) ->
        let env, { subst_type; subst_expr; _ } = bind_vars env vars in
        (* Remember: this is all in desugared form, so the variables in [args]
         * are all bound. *)
        let args = List.map subst_type args in
        let return_type = subst_type return_type in
        let body = subst_expr body in
        string "fun " ^^ lbracket ^^ join (comma ^^ space) (List.map print_binder vars) ^^
        rbracket ^^ jump (
          join break1 (List.map (print_type env) args)
        ) ^^ colon ^^ space ^^ print_type env return_type ^^ space ^^ equals ^^
        jump (print_expr env body)

    | EAssign (e1, f, e2) ->
        print_expr env e1 ^^ dot ^^ print_field f ^^ space ^^ larrow ^^ jump (print_expr env e2)

    | EAccess (e, f) ->
        print_expr env e ^^ dot ^^ print_field f

    | EApply (f, arg) ->
        let arg = print_expr env arg in
        let f = print_expr env f in
        f ^^ space ^^ arg

    | ETuple exprs ->
        let exprs = List.map (print_expr env) exprs in
        lparen ^^ join (comma ^^ space) exprs ^^ rparen

    | EMatch (e, patexprs) ->
        let patexprs = List.map (fun (pat, expr) ->
          let vars = collect_pattern pat in
          let bindings = List.map (fun v -> (v, KTerm)) vars in
          let env, { subst_expr; _ } = bind_vars env bindings in
          let expr = subst_expr expr in
          print_pat env pat ^^ space ^^ arrow ^^ jump (print_expr env expr)
        ) patexprs in
        string "match" ^^ space ^^ print_expr env e ^^ space ^^ string "with" ^^
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

    | EIfThenElse (e1, e2, e3) ->
        string "if" ^^ space ^^ print_expr env e1 ^^ space ^^ string "then" ^^
        jump (print_expr env e2) ^^ break1 ^^ string "else" ^^
        jump (print_expr env e3)

    | ELocated (e, _, _) ->
        print_expr env e

    | EPlus (e1, e2) ->
        print_expr env e1 ^^ space ^^ plus ^^ space ^^ print_expr env e2

    | EMinus (e1, e2) ->
        print_expr env e1 ^^ space ^^ minus ^^ space ^^ print_expr env e2

    | ETimes (e1, e2) ->
        print_expr env e1 ^^ space ^^ star ^^ space ^^ print_expr env e2

    | EDiv (e1, e2) ->
        print_expr env e1 ^^ space ^^ slash ^^ space ^^ print_expr env e2

    | EUMinus e ->
        minus ^^ print_expr env e

    | EInt i ->
        int i

  and print_rec_flag = function
    | Recursive ->
        string " rec"
    | Nonrecursive ->
        empty


  and print_binder (name, kind) =
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
    join
      (hardline ^^ hardline)
      declarations
  ;;

  let pdeclarations (env, declarations) =
    print_declarations env declarations
  ;;

end
