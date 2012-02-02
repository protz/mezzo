(* ---------------------------------------------------------------------------- *)

(* Syntactic categories of names. *)

(* Term variables, type variables, type constructors, fields are not
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

%token KTERM KTYPE KPERM
%token PERMISSION UNKNOWN DYNAMIC EXCLUSIVE
%token DATA BAR
%token LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token COMMA COLON COLONCOLON SEMI DBLARROW ARROW STAR
%token LARROW
%token EQUAL SEMISEMI
%token EMPTY
%token CONSUMES
%token VAL LET REC AND FUN IN DOT WITH BEGIN END MATCH
%token IF THEN ELSE
%token EOF

(* ---------------------------------------------------------------------------- *)

(* Miscellaneous directives. *)

%start <SurfaceSyntax.data_type_group * SurfaceSyntax.declaration_group> unit
%type <SurfaceSyntax.inner_declaration> inner_declaration
%type <SurfaceSyntax.expression> expression
%type <SurfaceSyntax.declaration> declaration

%{

open SurfaceSyntax

%}

%%

(* ---------------------------------------------------------------------------- *)

(* Namespaces. *)

(* We work with several namespaces, each of which is obtained by applying
   the functor [Identifier.Make] and defines an abstract type [name]. This
   should help us avoid confusions between namespaces: names for variables,
   data constructors, etc. have distinct types. *)

%inline variable:
  x = LIDENT
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

%inline atleast_two_list(sep, X):
| x1 = X sep x2 = separated_list(sep, X)
    { x1 :: x2 }

(* ---------------------------------------------------------------------------- *)

(* Syntax for tuples. *)

(* I considered using curly braces and semicolons, by analogy with
   records, but this would be too extreme: (1) it would impact the
   syntax of multiple-argument functions and (2) it would depart from
   the mathematical notation for tuples. *)

(* I thought for a moment that, in order to avoid a conflict with the
   standard use of parentheses as a desambiguation construct, tuples
   of length one would have to be made syntactically unavailable. I
   have changed my mind, because this position is untenable; tuples
   of length one are actually useful, e.g. in a function type of the
   form [(x: t) -> u] or [(consumes t) -> u]. So, my new position is,
   tuples are unrestricted, and there is no other use of parentheses.
   A post-processing phase determines how tuples of length one should
   be interpreted. *)

%inline tuple(X):
  LPAREN xs = separated_list(COMMA, X) RPAREN
    { xs }

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

(* Syntax for binding type variables. *)

(* Because the syntax of type/type applications is juxtaposition, the
   syntax of type variable bindings must be atomic (well-delimited). *)

atomic_type_binding:
| x = variable (* KTYPE is the default kind *)
    { x, KType }
| LPAREN b = type_binding RPAREN
    { b }

type_binding:
| b = atomic_type_binding
    { b }
| x = variable COLONCOLON kind = kind
    { x, kind }

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
(* We remove arrow kinds because they complicate the inference
   and expression of ``mode facts''. That is, in the presence
   of type variables of higher kinds, it becomes difficult to
   specify exactly under what conditions a type is duplicable,
   exclusive, or affine. Perhaps the loss of arrow kinds will
   be compensated by introducing a module system (functors, etc.)
   where facts can appear as module components.
| kind1 = atomic_kind ARROW kind2 = kind
    { KArrow (kind1, kind2) }
*)

(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

(* Because types and permissions are distinguished via the kind system, they
   are not (and must not be) distinguished in the syntax. Thus, the
   productions that concern permissions (the empty permission, anchored
   permissions, permission conjunction, etc.) appear as part of the syntax of
   types. *)

(* Tuple types follow the Haskell style [(typ, ..., typ)] and can introduce
   names for their components [(x: typ, ..., x: typ)]. Every name is bound in
   every component, so mutual dependencies are allowed. Furthermore, if a
   tuple type appears on the left-hand side of an arrow, then the scope of
   these bindings extends to the right-hand side of the arrow. Anyway, these
   scoping rules have no influence on the grammar per se. *)

(* Function types take the traditional form [typ -> typ]. It is possible to
   write a multi-argument dependent function type [(x: typ, ..., x: typ) ->
   ... ]: it is interpreted syntactically as a function type whose domain
   is a tuple type. *)

(* There is a potential ambiguity because the anchored permission [x: typ] is
   an anchored permission, hence a type (of kind [KPerm]). This means that
   [(x: typ)] can be interpreted either as a tuple type whose component is
   named [x] and has type [typ] or as a tuple type whose anonymous component
   has type [x: typ]. Fortunately, the second alternative does not make sense,
   because a type that serves as a tuple component must have kind
   [KType]. Thus, we adjust the syntax of tuple types so that the types that
   appear within tuples cannot be anchored permissions. *)

(* We allow a component of a tuple type to carry the [CONSUMES] keyword. This
   does not make sense in a normal tuple type, but makes sense if this tuple
   serves as a function argument. It is up to a post-processing phase to check
   that [CONSUMES] is used only where it makes sense, and to desugar it. *)

%inline tuple_type_component:
  m = function_parameter_modifier (* optional CONSUMES annotation *)
  a = tuple_type_component_aux
    { m, a }

(* The [CONSUMES] annotation is explicit, while the default is that
   (permissions for) function arguments are consumed and produced. *)

function_parameter_modifier:
| (* by default, permission is consumed and produced *)
    { ConsumesAndProduces }
| CONSUMES
    { Consumes }

(* A tuple type component can be either a value (which exists at runtime)
   or a permission. This is natural, because we allow the same flexibility
   in records, and because we need this flexibility in order to specify
   function domains and codomains. If it is a value, it can be either
   anonymous or named. *)

tuple_type_component_aux:
| x = ioption(terminated(variable, COLON)) (* an optional name for this component *)
  ty = normal_type                         (* a type for this component *)
    { TyTupleComponentValue (x, ty) }
| ty = permission_field_def                (* this component is an anonymous permission *)
    { TyTupleComponentPermission ty }

(* The syntax of types is stratified into the following levels, so as
   to eliminate all ambiguity. *)

atomic_type:
| tcs = tuple(tuple_type_component) (* tuple types à la Haskell; this includes the normal use of parentheses! *)
    { TyTuple tcs }
| UNKNOWN (* a type which means no permission; the top type *)
    { TyUnknown }
| DYNAMIC (* a type which means permission to test membership in a dynamic region *)
    { TyDynamic }
| EMPTY   (* the empty permission; neutral element for permission conjunction *)
    { TyEmpty }
| x = variable  (* term variable, type variable, permission variable, abstract type, or concrete type *)
    { TyVar x }
| b = data_type_def_branch (* concrete type with known branch *)
    { TyConcreteUnfolded b }
(* TEMPORARY inhabitants of static group regions *)

quasi_atomic_type:
| ty = atomic_type
    { ty }
| EQUAL x = variable (* singleton type *)
    { TySingleton (TyVar x) }
| ty = type_type_application(quasi_atomic_type, atomic_type) (* type application *)
    { ty }

type_parameters:
| LBRACKET bs = separated_or_terminated_list(COMMA, type_binding) RBRACKET
    { bs }

normal_type:
| ty = quasi_atomic_type
    { ty }
| ty1 = quasi_atomic_type ARROW ty2 = normal_type (* function type *)
    { TyArrow (ty1, ty2) }
| bs = type_parameters ty = normal_type (* polymorphic type *)
    { List.fold_right (fun b ty -> TyForall (b, ty)) bs ty }

loose_type:
| ty = normal_type
    { ty }
| p = anchored_permission (* anchored permission *)
    { let x, ty = p in TyAnchoredPermission (TyVar x, ty) }
(* TEMPORARY
   mode constraints as function preconditions and/or as tuple components?
   syntax for anonymous sums?
*)

(* I considered using COMMA for separating conjunction because this seems
   natural; think of the PRODUCES and CONSUMES clauses in function types.
   However, COMMA is already used to separate multiple arguments in a type
   application, so this means that parentheses will sometimes be necessary
   (e.g. when a conjunction of permissions is used as an argument in a type
   application). Even worse, COMMA is used in the syntax of tuples, and this
   leads to conflicts with tuple types and multi-argument function types.
   So, I give up and use a dedicated symbol, STAR, for conjunction. *)

very_loose_type:
| ty = loose_type
    { ty }
| ty1 = loose_type STAR ty2 = very_loose_type (* conjunction of permissions *)
    { TyStar (ty1, ty2) }

(* We distinguish anchored permissions, of the form [x: t], and
   general permissions, which are not necessarily anchored.
   General permissions are just types of kind KPERM. *)

(* In an anchored permission x: t, the variable x is free. This
   is not a binding form. However, anchored permissions are
   re-used as part of named field definitions, where they are
   viewed as a binding form. *)

anchored_permission:
| x = variable COLON ty = normal_type
    { x, ty }
| x = variable EQUAL y = variable (* x = y is sugar for x: =y *)
    { x, TySingleton (TyVar y) }

(* ---------------------------------------------------------------------------- *)

(* Data type definitions. *)

(* A named field definition binds a field name and at the same time
   specifies an anchored permission for it. *)
%inline named_field_def:
  p = anchored_permission
    { p }

permission_field_def:
  PERMISSION ty = very_loose_type (* a type of kind KPERM *)
    { ty }

data_field_def:
| p = named_field_def
    { FieldValue p }
| ty = permission_field_def
    { FieldPermission ty }
(* TEMPORARY
  adopts clauses
  mode assertions
  ... *)

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
(* TEMPORARY could allow datacon to be omitted if there is only one branch
   -- i.e. this is a record type *)

%inline data_type_flag:
| /* nothing */
  { Duplicable }
| EXCLUSIVE
  { Exclusive }

%inline data_type_def:
  flag = data_type_flag
  lhs = data_type_def_lhs
  EQUAL
  rhs = data_type_def_rhs
    { flag, lhs, rhs }

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
  | LPAREN ps = atleast_two_list(COMMA, pat1) RPAREN
      { PTuple ps }
  | dc = datacon_application(datacon, data_field_pat)
      { PConstruct dc }
  | LPAREN p = pat1 RPAREN
      { p }

    %inline data_field_pat:
    | f = variable EQUAL p = variable
        { f, p }

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
| e = expr1
    { e }

  (* Let-bindings *)
  %inline expr1:
  | e = elocated(raw_expr1)
      { e }

  raw_expr1:
  | LET f = rec_flag declarations = separated_list(AND, inner_declaration) IN e = expr1
      { ELet (f, declarations, e) }
  | e = raw_expr2
      { e }

  (* Type annotations, sequence, assignment *)
  %inline expr2:
  | e = elocated(raw_expr2)
      { e }

  raw_expr2:
  | e = expr3 COLON t = very_loose_type
      { EConstraint (e, t) }
  | e1 = expr2 SEMI e2 = expr3
      { ESequence (e1, e2) }
  | e1 = expr2 DOT f = variable LARROW e2 = expr3
      { EAssign (e1, f, e2) }
  | e = raw_expr3
      { e }

  (* Constructor *)
  %inline expr3:
  | e = elocated(raw_expr3)
      { e }

  (* OCaml parses { foo = let () = () in 1 };; and we don't. Too bad! *)
  raw_expr3:
  | dc = datacon_application(datacon, data_field_assign)
      { EConstruct dc }
  | e = raw_expr4
      { e }

    %inline data_field_assign:
    | f = variable EQUAL e = expr4
        { f, e }

  (* Application *)
  %inline expr4:
  | e = elocated(raw_expr4)
      { e }

  raw_expr4:
  | e1 = expr4 e2 = expr5
      { EApply (e1, e2) }
  | e = raw_expr5
      { e }

  (* If-then-else *)
  %inline expr5:
  | e = elocated(raw_expr5)
      { e }

  raw_expr5:
  | e = ifnoelse
      { e }
  | e = ifelse
      { e }
  | e = raw_expr6
      { e }

    ifnoelse:
    | IF e1 = expr5 THEN e2 = expr5
        { EIfThenElse (e1, e2, ETuple []) }

    ifelse:
    | IF e1 = expr5 THEN e2 = ifnoelse ELSE e3 = expr5
        { EIfThenElse (e1, e2, e3) }
    | IF e1 = expr5 THEN e2 = expr6 ELSE e3 = expr5
        { EIfThenElse (e1, e2, e3) }

  (* The rest *)
  %inline expr6:
  | e = elocated(raw_expr6)
      { e }

  raw_expr6:
  | v = variable
      { EVar v }
  | LPAREN es = atleast_two_list(COMMA, expr1) RPAREN
      { ETuple es }
  | MATCH e = expr1 WITH bs = separated_or_preceded_list(BAR, match_branch) END
      { EMatch (e, bs) }
  | BEGIN e = expr1 END
      { e }
  | LPAREN e = expr1 RPAREN
      { e }

    %inline match_branch:
    | p = pattern ARROW e = expr1
        { p, e }

(* ---------------------------------------------------------------------------- *)

(* Top-level declarations. *)

%inline dlocated (X):
| x = X
    { DLocated (x, $startpos, $endpos) }

(* A declaration group is a sequence of mutually recursive definitions separated
 * by ;;. We require the double-semicolon here (it may be made optional later)
 * in the hope that this makes parsing fail earlier, therefore giving better
 * error messages. *)
declaration_group:
| l = separated_list(SEMISEMI, declaration)
    { l }

%inline declaration:
| d = decl1
    { d }

%inline decl1:
| d = dlocated(raw_decl1)
    { d }

(* We use the keyword [val] for top-level declarations. *)
raw_decl1:
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
    { IValues (p, e) }
| f_name = variable bs = type_parameters? f_args = one_tuple+ COLON t = normal_type EQUAL e = expression
    { IFunction (f_name, Option.map_none [] bs, f_args, t, e) }

  %inline one_tuple:
  | tcs = tuple(tuple_type_component)
      { TyTuple tcs }

(* ---------------------------------------------------------------------------- *)

(* Program units. *)

unit:
  group = data_type_group
  declarations = declaration_group
  EOF
    { group, declarations }
