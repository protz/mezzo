(* ---------------------------------------------------------------------------- *)

(* Syntactic categories of names. *)

(* Term variables, type variables, type constructors, fields are not
   syntactically distinguished. Placing term variables, type variables, and
   type constructors within a single syntactic category is natural because
   they share certain mechanisms (e.g. types and terms can be abstracted over
   them). They will be distinguished using sorts. Placing term variables and
   fields within a single syntactic category is natural because we wish to
   allow puns. *)

%token LIDENT

(* As in ocaml, we set up a separate namespace for data constructors. This allows
   distinguishing variables and data constructors in a pattern. (Another solution
   would be to require data constructors to be explicitly followed with braces.) *)

%token UIDENT

(* ---------------------------------------------------------------------------- *)

(* Other tokens. *)

%token KTERM KTYPE KPERM
%token PERMISSION UNKNOWN DYNAMIC
%token DATA BAR
%token LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token COMMA COLON COLONCOLON SEMI ARROW STAR
%token EQUAL
%token EMPTY
(* %token WHERE CONSUMES PRODUCES *)
%token EOF

(* ---------------------------------------------------------------------------- *)

(* Miscellaneous directives. *)

%start<unit> unit

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

(* Tuples. *)

(* I would have liked to use curly braces and semicolons, by analogy with
   records, but this would be too extreme: (1) it would impact the syntax
   of multiple-argument functions and (2) it would depart from the mathematical
   notation for tuples. *)

tuple(X):
  LPAREN xs = separated_list(COMMA, X) RPAREN
    { xs }

(* In order to avoid a conflict with the standard use of parentheses as
   a desambiguation construct, tuples of length one must sometimes be
   made syntactically unavailable. *)

%inline nontrivial_tuple(X):
| LPAREN RPAREN (* tuple of length 0 *)
    { [] }
| LPAREN x = X COMMA xs = separated_nonempty_list(COMMA, X) RPAREN (* tuple of length 2 or greater *)
    { x :: xs }

(* ---------------------------------------------------------------------------- *)

(* Kinds. *)

kind0:
| LPAREN kind RPAREN
    {}
| KTERM
    {}
| KTYPE
    {}
| KPERM
    {}

kind:
| k = kind0
    { k }
| kind0 ARROW kind
    {}

(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

(* Because types and permissions are distinguished via the kind system,
   they are not (and must not be) distinguished in the syntax. Thus,
   the productions that concern permissions (the empty permission,
   anchored permissions, permission conjunction, etc.) appear as part
   of the syntax of types. *)

type_application(X, Y):
  X LBRACKET separated_nonempty_list(COMMA, Y) RBRACKET
    {}

type_binding:
  LIDENT COLONCOLON kind
    {}

(* Every function argument must come with a type. At worst, this type
   could be UNKNOWN, if one does not wish to specify a type. *)

function_parameters:
| typ0 (* TEMPORARY tuple(anchored_permission) *)
    {}

function_results:
  typ1 (* TEMPORARY *)
    {}

typ0:
| LPAREN typ RPAREN
    {}
| UNKNOWN (* a type which means no permission; the top type *)
    {}
| DYNAMIC (* a type which means permission to test membership in a dynamic region *)
    {}
| EMPTY   (* the empty permission; neutral element for permission conjunction *)
    {}
| LIDENT  (* term variable, type variable, permission variable, abstract type, or concrete type *)
    {}
| data_type_def_branch (* concrete type with known branch *)
    {}
| EQUAL LIDENT (* singleton type *)
    {}
| type_application(typ0, typ1)
    {}

typ1:
| t = typ0
    { t }
| function_parameters ARROW function_results
    {}
| anchored_permission
    {}
(* TEMPORARY
   function types; consumes/produces plus sugar
   polymorphic types
   syntax for anonymous tuples/sums?
*)

typ2:
| t = typ1
    { t }
| typ1 STAR typ2 (* conjunction of permissions *)
    {}

(* I considered using COMMA for separating conjunction because this seems
   natural; think of the PRODUCES and CONSUMES clauses in function types.
   However, COMMA is already used to separate multiple arguments in a type
   application, so this means that parentheses will sometimes be necessary
   (e.g. when a conjunction of permissions is used as an argument in a type
   application). Even worse, COMMA is used in the syntax of tuples, and this
   leads to conflicts with tuple types and multi-argument function types.
   So, I give up and use a dedicated symbol, STAR, for conjunction. *)

%inline typ:
  t = typ2
    { t }

(* We distinguish anchored permissions, of the form x: t, and
   general permissions, which are not necessarily anchored.
   General permissions are just types of kind KPERM. *)

(* In an anchored permission x: t, the variable x is free. This
   is not a binding form. However, anchored permissions are
   re-used as part of named field definitions, where they are
   viewed as a binding form. *)

anchored_permission:
| LIDENT COLON typ1
    {}
| LIDENT EQUAL LIDENT (* x = y is sugar for x: =y *)
    {}

(* ---------------------------------------------------------------------------- *)

(* Data type definitions. *)

(* TEMPORARY allow exclusive/mutable declarations *)

datacon:
  UIDENT
    {}

(* A named field definition binds a field name and at the same time
   specifies an anchored permission for it. *)
named_field_def:
  anchored_permission
    {}

permission_field_def:
  PERMISSION typ (* a type of kind KPERM *)
    {}

data_field_def:
| named_field_def
    {}
| permission_field_def
    {}
(* TEMPORARY
  adopts clauses
  mode assertions
  ... *)

datacon_application(X, Y):
| X (* a pair of empty braces can be omitted *)
    {}
| X LBRACE separated_or_terminated_list(SEMI, Y) RBRACE
    {}

data_type_def_branch:
  datacon_application(datacon, data_field_def)
    {}

data_type_def_lhs:
  DATA type_application(LIDENT, type_binding)
    {}

data_type_def_rhs:
  separated_or_preceded_list(BAR, data_type_def_branch)
    {}

data_type_def:
  data_type_def_lhs
  data_type_def_rhs
    {}

(* ---------------------------------------------------------------------------- *)

(* Terms. *)

(* ---------------------------------------------------------------------------- *)

(* Program units. *)

unit:
  data_type_def*
  EOF
    {}
