(* ---------------------------------------------------------------------------- *)

(* Syntactic categories of names. *)

(* Term variables, type variables, type constructors, and fields are not
   syntactically distinguished. Placing term variables, type variables, and
   type constructors within a single syntactic category is natural because
   they share certain mechanisms (e.g. types and terms can be abstracted over
   them). They will be distinguished using sorts. Placing term variables and
   fields within a single syntactic category is required because we wish to
   allow puns. *)

%token<string> LIDENT

(* As in ocaml, we set up a separate namespace for data constructors. This allows
   distinguishing variables and data constructors in a pattern. (Another solution
   would be to require data constructors to be explicitly followed with braces.) *)

%token<string> UIDENT

(* ---------------------------------------------------------------------------- *)

(* Other tokens. *)

%token          KTERM KTYPE KPERM
%token          PERMISSION UNKNOWN DYNAMIC EXCLUSIVE
%token          DATA BAR
%token          LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token          COMMA COLON COLONCOLON SEMI STAR AT
%token          ARROW LARROW DBLARROW DBLLARROW FUN
%token          EQUAL
%token          EMPTY ASSERT EXPLAIN FAIL
%token          CONSUMES DUPLICABLE FACT ABSTRACT
%token          VAL LET REC AND IN DOT WITH BEGIN END MATCH
%token          IF THEN ELSE
%token<int>     INT
%token          MINUS
%token<string>  OPPREFIX OPINFIX0 OPINFIX1 OPINFIX2 OPINFIX3
%token          EOF

%nonassoc THEN
%nonassoc ELSE

%left     OPINFIX0 MINUS
%right    OPINFIX1
%left     OPINFIX2
%left     OPINFIX3

(* ---------------------------------------------------------------------------- *)

(* Miscellaneous directives. *)

%start <SurfaceSyntax.program> unit
%type <SurfaceSyntax.expression> expression
%type <SurfaceSyntax.declaration> declaration

%{

open SurfaceSyntax

let mkinfix e1 o e2 = EApply (EVar (Variable.register o), ETuple [e1; e2]);;

%}

%%

(* ---------------------------------------------------------------------------- *)

(* Namespaces. *)

(* We work with several namespaces, each of which is obtained by applying
   the functor [Identifier.Make] and defines an abstract type [name]. This
   should help us avoid confusions between namespaces: names for variables,
   data constructors, etc. have distinct types. *)

%inline operator:
  | o = OPPREFIX
  | o = OPINFIX0
  | o = OPINFIX1
  | o = OPINFIX2
  | o = OPINFIX3
    { o }
  | STAR
    { "*" }
  | MINUS
    { "-" }

%inline variable:
  | x = LIDENT
  | LPAREN x = operator RPAREN
    { Variable.register x }

%inline datacon:
  datacon = UIDENT
    { Datacon.register datacon }

(* ---------------------------------------------------------------------------- *)

(* Flexible lists. *)

separated_or_terminated_list(sep, X):
| (* nothing *)
    { [] }
| xs = terminated(X, sep)+
| xs = separated_nonempty_list(sep, X)
    { xs }

separated_or_preceded_list(sep, X):
| (* nothing *)
    { [] }
| xs = preceded(sep, X)+
| xs = separated_nonempty_list(sep, X)
    { xs }

%inline separated_list_of_at_least_two(sep, X):
| x1 = X sep x2 = separated_list(sep, X)
    { x1 :: x2 }

(* ---------------------------------------------------------------------------- *)

(* Syntax for type/type applications. *)

(* Applications of types to types are based on juxtaposition, just like
   applications of terms to terms. *)

(* Within the syntax of types, type/type applications are considered
   binary, but in certain places, as in the left-hand side of a data
   type definition, we must allow iterated applications. *)

%inline type_type_application(X, Y):
  ty1 = X ty2 = Y (* juxtaposition *)
    { TyApp (ty1, ty2) }

%inline iterated_type_type_application(X, Y):
  x = X ys = Y* (* iterated juxtaposition *)
    { x, ys }

(* ---------------------------------------------------------------------------- *)

(* Syntax for type abstraction and universal quantification. *)

type_parameters:
| LBRACKET bs = separated_or_terminated_list(COMMA, type_binding) RBRACKET
    { bs }

(* ---------------------------------------------------------------------------- *)

(* Syntax for binding type variables. *)

(* Because the syntax of type/type applications is juxtaposition, the
   syntax of type variable bindings must be atomic (well-delimited). *)

atomic_type_binding:
| x = variable (* KTYPE is the default kind *)
    { x, KType, ($startpos, $endpos) }
| LPAREN b = type_binding RPAREN
    { b }

type_binding:
| b = atomic_type_binding
    { b }
| x = variable COLONCOLON kind = kind
    { x, kind, ($startpos, $endpos) }

(* ---------------------------------------------------------------------------- *)

(* Kinds. *)

atomic_kind:
| LPAREN kind = kind RPAREN
    { kind }
| KTERM
    { KTerm }
| KTYPE
    { KType }
| KPERM
    { KPerm }

%inline kind:
| kind = atomic_kind
    { kind }

(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

(* Because types and permissions are distinguished via the kind system, they
   are not (and must not be) distinguished in the syntax. Thus, the
   productions that concern permissions (the empty permission, anchored
   permissions, permission conjunction, etc.) appear as part of the syntax of
   types. *)

(* The syntax of types is stratified into the following levels, so as to
   eliminate all ambiguity. *)

%inline tlocated (X):
| x = X
    { TyLocated (x, $startpos, $endpos) }

%inline atomic_type:
| t = tlocated(raw_atomic_type)
  { t }

  raw_atomic_type:
  (* The empty tuple type. *)
  | LPAREN RPAREN
      { TyTuple [] }
  (* Parentheses are used as a disambiguation device, as is standard. *)
  | LPAREN t = arbitrary_type RPAREN
      { t }
  (* The top type. *)
  | UNKNOWN
      { TyUnknown }
  (* The type [dynamic] represents a permission to test membership in a dynamic region. *)
  | DYNAMIC
      { TyDynamic }
  (* The top permission. A neutral element for permission conjunction. *)
  | EMPTY
      { TyEmpty }
  (* Term variable, type variable, permission variable, abstract type, or concrete type. *)
  | x = variable
      { TyVar x }
  (* A structural type explicitly mentions a data constructor. *)
  | b = data_type_def_branch
      { TyConcreteUnfolded b }

%inline quasi_atomic_type:
| t = tlocated(raw_quasi_atomic_type)
  { t }

  raw_quasi_atomic_type:
  | ty = raw_atomic_type
      { ty }
  (* A singleton type. *)
  | EQUAL x = variable
      { TySingleton (TyVar x) }
  (* A type application. *)
  | ty = type_type_application(quasi_atomic_type, atomic_type)
      { ty }

%inline normal_type:
| t = tlocated(raw_normal_type)
  { t }

  %inline duplicity_constraint:
  | EXCLUSIVE t = quasi_atomic_type
      { Exclusive, t }
  | DUPLICABLE t = quasi_atomic_type
      { Duplicable, t }

  %inline raw_constrained_type:
  | LPAREN dc = separated_nonempty_list (COMMA, duplicity_constraint) RPAREN DBLARROW ty = normal_type
      { TyConstraints (dc, ty) }

  %inline constrained_type:
  | t = tlocated(raw_constrained_type)
    { t }

  %inline constrained_or_atomic_type:
  | ty = constrained_type
      { ty }
  | ty = atomic_type
      { ty }

  raw_normal_type:
  | ty = raw_quasi_atomic_type
      { ty }
  (* The syntax of function types is [t -> t], as usual. *)
  | ty1 = quasi_atomic_type ARROW ty2 = normal_type
      { TyArrow (ty1, ty2) }
  (* A polymorphic type. *)
  | bs = type_parameters ty = normal_type
      { List.fold_right (fun b ty -> TyForall (b, ty)) bs ty }
  | ty = raw_constrained_type
      { ty }

%inline loose_type:
| t = tlocated(raw_loose_type)
  { t }

  raw_loose_type:
  | ty = raw_normal_type
      { ty }
  (* In an anchored permission [x@t], the name [x] is free. This
     represents an assertion that we have permission to use [x] at
     type [t]. *)
  | x = variable AT ty = normal_type
      { TyAnchoredPermission (TyVar x, ty) }
  (* [x = y] is also an anchored permission; it is sugar for [x@=y]. *)
  | x = variable EQUAL y = variable
      { TyAnchoredPermission (TyVar x, TySingleton (TyVar y)) }
  (* In a name introduction form [x:t], the name [x] is bound. The scope
     of [x] is defined by somewhat subtle rules that need not concern us
     here. These rules are spelled out later on when we desugar the surface-level
     types into a lower-level representation. *)
  | x = variable COLON ty = normal_type
      { TyNameIntro (x, ty) }

%inline consumes_type:
| t = tlocated(raw_consumes_type)
  { t }

  raw_consumes_type:
  | ty = raw_loose_type
      { ty }
  (* A type can be annotated with the [CONSUMES] keyword. This really
     makes sense only in certain contexts, e.g. in the left-hand side of an
     arrow, and possibly further down under tuples, stars, etc. The grammar
     allows this everywhere. This notation is checked for consistency and
     desugared in a separate pass. *)
  | CONSUMES ty = loose_type
      { TyConsumes ty }

%inline very_loose_type:
| t = tlocated(raw_very_loose_type)
  { t }

  raw_very_loose_type:
  | ty = raw_consumes_type
      { ty }
  (* Permission conjunction is a binary operator. *)
  | ty1 = consumes_type STAR ty2 = very_loose_type
      { TyStar (ty1, ty2) }
  (* A tuple type of length at least two is written [t1, ..., tn], without
     parentheses. A tuple type of length one cannot be written -- there is
     no syntax for it. *)
  | tcs = separated_list_of_at_least_two(COMMA, consumes_type)
      { TyTuple tcs }

%inline fat_type:
| t = tlocated(raw_fat_type)
  { t }

  raw_fat_type:
  | ty = raw_very_loose_type
      { ty }
  (* The conjunction of a type and a permission is written [t | p]. It is
     typically used as the domain or codomain of a function type. *)
  | ty1 = fat_type BAR ty2 = very_loose_type
      { TyBar (ty1, ty2) }
  | BAR ty2 = very_loose_type
      { TyBar (TyTuple [], ty2) }

%inline arbitrary_type:
  t = fat_type
    { t }

(* ---------------------------------------------------------------------------- *)

(* Data type definitions. *)

data_field_def:
(* A named field definition binds a field name and at the same time
   specifies an anchored permission for it. *)
| x = variable COLON ty = normal_type
    { FieldValue (x, ty) }
(* A permission field is anonymous. *)
(* TEMPORARY use the new BAR syntax here; remove PERMISSION keyword *)
| PERMISSION ty = arbitrary_type (* a type of kind KPERM *)
    { FieldPermission ty }

datacon_application(X, Y):
| x = X (* a pair of empty braces can be omitted *)
    { x, [] }
| x = X LBRACE ys = separated_or_terminated_list(SEMI, Y) RBRACE
    { x, ys }

%inline data_type_def_branch:
  dfs = datacon_application(datacon, data_field_def)
    { dfs }

%inline data_type_def_lhs:
  DATA tbs = iterated_type_type_application(variable, atomic_type_binding)
    { tbs }

%inline data_type_def_rhs:
  bs = separated_or_preceded_list(BAR, data_type_def_branch)
    { bs }

%inline data_type_flag:
| (* nothing *)
    { Duplicable }
| EXCLUSIVE
    { Exclusive }

%inline optional_kind_annotation:
| (* nothing *)
    { KType }
| COLONCOLON k = kind
    { k }

%inline fact_conditions:
| (* nothing *)
    { [] }
| DUPLICABLE t = atomic_type DBLARROW
    { [t] }
(* TEMPORARY la syntaxe de fact_conditions/fact me semble trop restrictive? *)

fact:
| FACT tup = fact_conditions DUPLICABLE t = arbitrary_type
    { FDuplicableIf (tup, t) }
| FACT EXCLUSIVE t = arbitrary_type
    { FExclusive t }

%inline data_type_def:
| flag = data_type_flag lhs = data_type_def_lhs EQUAL rhs = data_type_def_rhs
    { Concrete (flag, lhs, rhs) }
| ABSTRACT name = variable params = atomic_type_binding*
  k = optional_kind_annotation f = fact?
    { Abstract ((name, params), k, f) }

%inline data_type_group:
  defs = data_type_def*
    { defs }

(* A concrete data type is necessarily of kind KTYPE. We do not allow defining
   concrete data types of kind KPERM. In principle, we could allow it. I think
   we can live without it (experience will tell). *)

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

%inline plocated (X):
| x = X
    { PLocated (x, $startpos, $endpos) }

%inline pattern:
| p = pat1
    { p }

  %inline pat1:
  | p = plocated(raw_pat1)
      { p }

  raw_pat1:
  | LPAREN p = pat1 COLON t = normal_type RPAREN
      { PConstraint (p, t) }
  | x = variable
      { PVar x }
  | LPAREN ps = separated_list_of_at_least_two(COMMA, pat1) RPAREN
      { PTuple ps }
  | dc = datacon_application(datacon, data_field_pat)
      { PConstruct dc }
  | LPAREN p = pat1 RPAREN
      { p }

    %inline data_field_pat:
    | f = variable EQUAL p = pattern
        { f, p }
    | f = variable
        (* Punning *)
        { f, PVar f }

(* ---------------------------------------------------------------------------- *)

(* Terms. *)

%inline rec_flag:
| REC
    { Recursive }
|
    { Nonrecursive }

%inline elocated (X):
| x = X
    { ELocated (x, $startpos, $endpos) }

(* Main expression rule *)
%inline expression:
| e = elocated(expression_raw)
    { e }

  expression_raw:
  | e1 = everything_except_let_and_semi SEMI e2 = expression
      { ESequence (e1, e2) }
  | LET f = rec_flag declarations = separated_list(AND, inner_declaration) IN e = expression
      { ELet (f, declarations, e) }
  | FUN bs = type_parameters? arg = atomic_type COLON t = normal_type EQUAL e = expression
      { EFun (Option.map_none [] bs, arg, t, e) }
  | e = everything_except_let_and_semi_raw
      { e }

  everything_except_let_and_semi:
  | e = elocated(everything_except_let_and_semi_raw)
      { e }

  everything_except_let_and_semi_raw:
  (* disallow let inside of "then", too fragile *)
  | IF b = explain e1 = expression THEN e2 = everything_except_let_and_semi
      { EIfThenElse (b, e1, e2, ETuple []) }
  | IF b = explain e1 = expression THEN e2 = everything_except_let_and_semi ELSE e3 = everything_except_let_and_semi
      { EIfThenElse (b, e1, e2, e3) }
  (* cannot allow let because right-hand side of let can contain a semi-colon *)
  | e1 = atomic DOT f = variable LARROW e2 = everything_except_let_and_semi
      { EAssign (e1, f, e2) }
  (* This generates a conflict. *)
  (* | e1 = atomic LARROW d = datacon_application(datacon, data_field_assign)
      { assert false } *)
  | e1 = atomic DBLLARROW d = datacon
      { EAssignTag (e1, d) }
  | e = explained_raw
      { e }

  explained_raw:
  | e = prefix_op EXPLAIN
      { EExplained e }
  | e = prefix_op_raw
      { e }

  (* Arithmetic expressions... *)
  %inline prefix_op:
  | e = elocated(prefix_op_raw)
      { e }

  prefix_op_raw:
  | MINUS e = prefix_op
      { mkinfix (EInt 0) "-" e }
  | o = OPPREFIX e = prefix_op
      { EApply (EVar (Variable.register o), e) }
  | e = infix_op_raw
      { e }

  %inline infix_op:
  | e = elocated(infix_op_raw)
      { e }

  infix_op_raw:
  | e1 = infix_op o = OPINFIX0 e2 = infix_op
      { mkinfix e1 o e2 }
  | e1 = infix_op o = OPINFIX1 e2 = infix_op
      { mkinfix e1 o e2 }
  | e1 = infix_op o = OPINFIX2 e2 = infix_op
      { mkinfix e1 o e2 }
  | e1 = infix_op o = OPINFIX3 e2 = infix_op
      { mkinfix e1 o e2 }
  | e1 = infix_op MINUS e2 = infix_op
      { mkinfix e1 "-" e2 }
  | e = app_raw
      { e }

  (* Application *)
  %inline app:
  | e = elocated(app_raw)
      { e }

  app_raw:
  | e1 = app e2 = atomic
      { EApply (e1, e2) }
  | e1 = app LBRACKET ts = separated_nonempty_list(COMMA, normal_type) RBRACKET
      { ETApply (e1, ts) }
  | e = atomic_raw
      { e }

  (* Tightly-knit productions *)
  %inline atomic:
  | e = elocated(atomic_raw)
      { e }

  explain:
  |
      { false }
  | EXPLAIN
      { true }

  atomic_raw:
  | v = variable
      { EVar v }
  | i = INT
      { EInt i }
  | FAIL
      { EFail }
  | dc = datacon_application(datacon, data_field_assign)
      { EConstruct dc }
  | LPAREN es = separated_list_of_at_least_two(COMMA, expression) RPAREN
      { ETuple es }
  | LPAREN RPAREN
      { ETuple [] }
  | MATCH b = explain e = expression WITH bs = separated_or_preceded_list(BAR, match_branch) END
      { EMatch (b, e, bs) }
  | e = atomic DOT f = variable
      { EAccess (e, f) }
  | BEGIN e = expression END
      { e }
  | LPAREN e = expression COLON t = arbitrary_type RPAREN
      { EConstraint (e, t) }
  | ASSERT LPAREN t = arbitrary_type RPAREN
      { EAssert t }
  | LPAREN e = expression RPAREN
      { e }

    %inline data_field_assign:
    (* cannot allow let because right-hand side of let can contain a semi-colon *)
    | f = variable EQUAL e = everything_except_let_and_semi
        { f, e }
    | f = variable
        (* Punning *)
        { f, EVar f }

    %inline match_branch:
    | p = pattern ARROW e = expression
        { p, e }

(* ---------------------------------------------------------------------------- *)

(* Top-level declarations. *)

%inline dlocated (X):
| x = X
    { DLocated (x, $startpos, $endpos) }

(* A declaration group is a sequence of mutually recursive definitions. *)
declaration_group:
| l = declaration*
    { l }

%inline declaration:
| d = dlocated(decl_raw)
    { d }

(* We use the keyword [val] for top-level declarations. *)
decl_raw:
| VAL flag = rec_flag declarations = separated_list(AND, inner_declaration)
    { DMultiple (flag, declarations) }

(* ---------------------------------------------------------------------------- *)

(* Inner declarations, also used by let-bindings. *)

(* We make a distinction between a single pattern and a function definition. The
 * former encompasses idioms such as [val x,y = ...]. The latter allows one to
 * define a function. There are additional rules that ought to be verified at
 * some point (e.g. only variables are allowed on the left-hand side of a
 * let-rec *)
inner_declaration:
| p = pattern EQUAL e = expression
    { p, e }
| f_name = variable bs = type_parameters? arg = constrained_or_atomic_type COLON t = normal_type EQUAL e = expression
    { PVar f_name, EFun (Option.map_none [] bs, arg, t, e) }

(* ---------------------------------------------------------------------------- *)

(* Program units. *)

unit:
  group = data_type_group
  declarations = declaration_group
  EOF
    { group, declarations }

(* ---------------------------------------------------------------------------- *)

(* Below this line: ideas for the record or for future consideration. *)

(* We have removed arrow kinds because they complicate the inference and
   expression of ``mode facts''. That is, in the presence of type variables of
   higher kinds, it becomes difficult to specify exactly under what conditions
   a type is duplicable, exclusive, or affine. Perhaps the loss of arrow kinds
   will be compensated by introducing a module system (functors, etc.) where
   facts can appear as module components. *)

(* If the [if] construct was closed with [endif], then one could again
   authorize a [let] construct to appear naked within a [then] or [else]
   branch. *)

(* I considered using COMMA for separating conjunction. However, COMMA is
   already used to separate multiple arguments in a type application, so this
   means that parentheses will sometimes be necessary (e.g. when a conjunction
   of permissions is used as an argument in a type application). Even worse,
   COMMA is used in the syntax of tuples, and this leads to conflicts with
   tuple types and multi-argument function types. So, I give up and use a
   dedicated symbol, STAR, for conjunction. Somewhat analogously, yet another
   symbol, BAR, is now used for the conjunction of a type and a permission. *)

(* ---------------------------------------------------------------------------- *)

(* Below this line: things to do. *)

(* TODO *)

(*
   mode constraints as function preconditions and as tuple/record components
   syntax for anonymous sums?
   adopts clauses
*)

