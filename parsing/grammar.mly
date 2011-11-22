(* ---------------------------------------------------------------------------- *)

(* Syntactic categories of names. *)

(* We assume that names are hash-consed (or internalized, in Java parlance)
   on the fly by the lexer, so the lexer produces integer codes for names. *)

(* Term variables, type variables, type constructors, fields are not
   syntactically distinguished. Placing term variables, type variables, and
   type constructors within a single syntactic category is natural because
   they share certain mechanisms (e.g. types and terms can be abstracted over
   them). They will be distinguished using sorts. Placing term variables and
   fields within a single syntactic category is natural because we wish to
   allow puns. *)

%token<int> LIDENT

(* As in ocaml, we set up a separate namespace for data constructors. This allows
   distinguishing variables and data constructors in a pattern. (Another solution
   would be to require data constructors to be explicitly followed with braces.) *)

%token<int> UIDENT

(* ---------------------------------------------------------------------------- *)

(* Other tokens. *)

%token KTERM KTYPE KPERM
%token PERMISSION UNKNOWN DYNAMIC
%token DATA BAR
%token LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token COMMA COLON COLONCOLON SEMI ARROW STAR
%token EQUAL
%token EMPTY
%token CONSUMES
%token EOF

(* ---------------------------------------------------------------------------- *)

(* Miscellaneous directives. *)

%start<SurfaceSyntax.data_type_group> unit

%{

open SurfaceSyntax

%}

%%

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

(* ---------------------------------------------------------------------------- *)

(* Syntax for tuples. *)

(* I would have liked to use curly braces and semicolons, by analogy with
   records, but this would be too extreme: (1) it would impact the syntax
   of multiple-argument functions and (2) it would depart from the mathematical
   notation for tuples. *)

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
| x = LIDENT (* KTYPE is the default kind *)
    { x, KType }
| LPAREN b = type_binding RPAREN
    { b }

type_binding:
| b = atomic_type_binding
    { b }
| x = LIDENT COLONCOLON kind = kind
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

kind:
| kind = atomic_kind
    { kind }
| kind1 = atomic_kind ARROW kind2 = kind
    { KArrow (kind1, kind2) }

(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

(* Because types and permissions are distinguished via the kind system, they
   are not (and must not be) distinguished in the syntax. Thus, the
   productions that concern permissions (the empty permission, anchored
   permissions, permission conjunction, etc.) appear as part of the syntax of
   types. *)

(* It seems difficult to avoid conflicts in the syntax of function
   types. One sure thing is, we wish to allow traditional function types of
   the form [typ -> typ], because these will remain common.  However, we
   also want to allow multi-argument dependent function types, of the form
   [(x: typ, ..., x: typ) -> ... ]. As a consequence, it seems that we must
   view [(x: typ, ..., x:typ)] as a type. Since the syntax of tuple types is
   [(typ, ..., typ)], it seems that we must identify these two forms, that
   is, we must allow tuple types that bind names for their
   components. Finally, there is an artificial ambiguity because (x: typ) is
   a type (of kind KPerm). It is not a real ambiguity because the tuple type
   [(x: typ, ..., x: typ)] is ill-kinded if each (x: typ) is viewed as a
   permission. We must simply adjust the syntax of tuple types so that the
   types that appear within tuples cannot be anchored permissions. In
   conclusion, we allow a component of a tuple type to be optionally
   named. It is up to a post-processing phase to determine what this name
   means and how it be should de-sugared into normal tuple types. For the
   same reason, we allow a component of a tuple type to carry the [CONSUMES]
   keyword. This does not make sense in a normal tuple type, but makes sense
   if this tuple serves as a function argument. *)

(* Every function argument is optionally annotated with [CONSUMES]. Every
   function argument must come with a type. At worst, this type can be
   [UNKNOWN], if one does not really wish to specify a type. *)

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
|                                 (* no name: this is the normal case *)
  ty = normal_type               (* type *)
    { TyTupleComponentAnonymousValue ty }
| x = LIDENT COLON                (* a name: this is allowed under the left-hand side of an arrow *)
  ty = normal_type               (* type *)
    { TyTupleComponentNamedValue (x, ty) }
| ty = permission_field_def       (* permission *)
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
| x = LIDENT  (* term variable, type variable, permission variable, abstract type, or concrete type *)
    { TyVar x }
| b = data_type_def_branch (* concrete type with known branch *)
    { TyConcreteUnfolded b }
(* TEMPORARY inhabitants of static group regions *)

quasi_atomic_type:
| ty = atomic_type
    { ty }
| EQUAL x = LIDENT (* singleton type *)
    { TySingleton x }
| ty = type_type_application(quasi_atomic_type, atomic_type) (* type application *)
    { ty }

normal_type:
| ty = quasi_atomic_type
    { ty }
| ty1 = quasi_atomic_type ARROW ty2 = normal_type (* function type *)
    { TyArrow (ty1, ty2) }
| LBRACKET bs = separated_or_terminated_list(COMMA, type_binding) RBRACKET ty = normal_type (* polymorphic type *)
    { List.fold_right (fun b ty -> TyForall (b, ty)) bs ty }

loose_type:
| ty = normal_type
    { ty }
| p = anchored_permission (* anchored permission *)
    { TyAnchoredPermission p }
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
| x = LIDENT COLON ty = normal_type
    { x, ty }
| x = LIDENT EQUAL y = LIDENT (* x = y is sugar for x: =y *)
    { x, TySingleton y }

(* ---------------------------------------------------------------------------- *)

(* Data type definitions. *)

(* TEMPORARY allow exclusive/mutable declarations *)

%inline datacon:
  d = UIDENT
    { d }

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
  DATA tbs = iterated_type_type_application(LIDENT, atomic_type_binding)
    { tbs }

%inline data_type_def_rhs:
  bs = separated_or_preceded_list(BAR, data_type_def_branch)
    { bs }

%inline data_type_def:
  lhs = data_type_def_lhs
  rhs = data_type_def_rhs
    { lhs, rhs }

%inline data_type_group:
  defs = data_type_def*
    { defs }

(* A concrete data type is necessarily of kind KTYPE. We do not allow defining
   concrete data types of kind KPERM. In principle, we could allow it. I think
   we can live without it (experience will tell). *)

(* ---------------------------------------------------------------------------- *)

(* Terms. *)

(* ---------------------------------------------------------------------------- *)

(* Program units. *)

unit:
  group = data_type_group
  EOF
    { group }
