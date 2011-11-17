(* ---------------------------------------------------------------------------- *)

(* Syntactic categories of names. *)

(* Term variables, type variables, type constructors, fields are not syntactically
   distinguished. *)

%token LIDENT

(* As in ocaml, we set up a separate namespace for data constructors. This allows
   distinguishing variables and data constructors in a pattern. (Another solution
   would be to require data constructors to be explicitly followed with braces.) *)

%token UIDENT

(* ---------------------------------------------------------------------------- *)

(* Other tokens. *)

%token PERMISSION UNKNOWN DYNAMIC
%token DATA BAR
%token LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token COMMA COLON SEMI ARROW
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

(* ---------------------------------------------------------------------------- *)

(* Types. *)

tycon:
  LIDENT
    {}

type_application(X, Y):
  X LBRACKET separated_list(COMMA, Y) RBRACKET
    {}

concrete_type:
  type_application(tycon, typ)
    {}

typ:
| UNKNOWN (* no permission *)
    {}
| DYNAMIC (* permission to test membership in a dynamic region *)
    {}
| tycon   (* type variable, abstract type, or concrete type *)
    {}
| type_application(typ, typ)
    {}
| data_type_def_branch (* concrete type with known branch *)
    {}
(*| function_parameters ARROW function_results
   {} *)
(* TEMPORARY
   function types; consumes/produces plus sugar
   ghost function parameters
   polymorphic types
   syntax for anonymous tuples/sums?
   forms that require term variables within types:
   =x
   t@x
   non-closed function types *)

(* A permission mentions a variable, which is free. This is not a
   binding form. *)
permission:
  var COLON typ
    {}
(* TEMPORARY
  permission variables *)

(* ---------------------------------------------------------------------------- *)

(* Data type definitions. *)

(* TEMPORARY allow exclusive/mutable declarations *)

datacon:
  UIDENT
    {}

field:
  LIDENT
    {}

(* A named field definition binds a field name and at the same time
   specifies a permission for it. *)
named_field_def:
  field COLON typ
    {}
(* TEMPORARY sugar: f = x for f: (=x)
             sugar: f for f = f *)

permission_field_def:
  PERMISSION permission
    {}

data_field_def:
| named_field_def
    {}
| permission_field_def
    {}
(* TEMPORARY
  adopts clauses
  mode assertions
  type equality constraints
  ghost fields
  ... *)

datacon_application(X, Y):
| X
    {}
| X LBRACE separated_list(SEMI, Y) RBRACE
    {}

data_type_def_branch:
  datacon_application(datacon, data_field_def)
    {}

data_type_def_lhs:
  DATA concrete_type
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

var:
  LIDENT
    {}

(* ---------------------------------------------------------------------------- *)

(* Program units. *)

unit:
  data_type_def*
  EOF
    {}
