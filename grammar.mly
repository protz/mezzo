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
%token CONSUMES
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

(* I thought for a moment that, in order to avoid a conflict with the
   standard use of parentheses as a desambiguation construct, tuples
   of length one would have to be made syntactically unavailable. I
   have changed my mind, because this position is untenable; tuples
   of length one are actually useful, e.g. in a function type of the
   form [(x: t) -> u] or [(consumes t) -> u]. So, my new position is,
   tuples are unrestricted, and there is no other use of parentheses.
   A post-processing phase determines how tuples of length one should
   be interpreted. *)

tuple(X):
  LPAREN xs = separated_list(COMMA, X) RPAREN
    { xs }

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

(* The syntax of type applications involves square brackets and commas.
   This can be viewed as noisy; perhaps one would prefer to simply use
   juxtaposition, as in applications of terms to terms. Within the
   syntax of types, this would be possible. However, within the syntax
   of terms, we will need to distinguish between an application of a
   term to a type and an application of a term to a term. So we might
   as well use square brackets wherever something is applied to a type. *)
(* TEMPORARY change this decision? *)

type_application(X, Y):
  X LBRACKET separated_nonempty_list(COMMA, Y) RBRACKET
    {}

type_binding:
| LIDENT (* KTYPE is the default kind *)
    {}
| LIDENT COLONCOLON kind
    {}

(* Every function argument must come with a type. At worst, this type
   could be UNKNOWN, if one does not wish to specify a type. *)

(* It seems difficult to avoid conflicts in the syntax of function types. One
   sure thing is, we wish to allow traditional function types of the form [typ
   -> typ], because these will remain common.  However, we also want to allow
   multi-argument dependent function types, of the form [(x: typ, ..., x: typ)
   -> ... ]. As a consequence, it seems that we must view [(x: typ, ...,
   x:typ)] as a type. Since the syntax of tuple types is [(typ, ..., typ)], it
   seems that we must identify these two forms, that is, we must allow tuple
   types that bind names for their components. Finally, there is an artificial
   ambiguity because (x: typ) is a type (of kind KPERM). It is not a real
   ambiguity because the tuple type of the form [(x: typ, ..., x: typ)] is
   ill-kinded if each (x: typ) is viewed as a permission. We must simply
   adjust the syntax of tuple types so that the types that appear within
   tuples cannot be anchored permissions. In conclusion, we allow a component
   of a tuple type to be optionally named. It is up to a post-processing phase
   to determine what this name means and how it be should de-sugared into
   normal tuple types. For the same reason, we allow a component of a tuple
   type to carry the [CONSUMES] keyword. This does not make sense in a normal
   tuple type, but makes sense if this tuple serves as a function argument. *)

%inline function_parameter_modifier: (* %inline required *)
| (* by default, permission is consumed and produced *)
    {}
| CONSUMES
    {}

%inline tuple_type_component_name: (* %inline required *)
| (* unnamed: this is the normal case *)
    {}
| LIDENT COLON (* named: this tuple is presumably used as argument or result of a function type *)
    {}

(* A tuple type component can be either a value (which exists at runtime)
   or a permission. This is natural, because we allow the same flexibility
   in records, and because we need this flexibility in order to specify
   function domains and codomains. *)

tuple_type_component:
  function_parameter_modifier (* optional CONSUMES annotation *)
  tuple_type_component_name   (* optional name *)
  typ1                        (* type *)
    {}
| function_parameter_modifier (* optional CONSUMES annotation *)
  permission_field_def        (* permission *)
    {}

typ0:
| tuple(tuple_type_component) (* tuple types à la Haskell; this includes the normal use of parentheses! *)
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
| type_application(typ0, typ3)
    {}
(* TEMPORARY inhabitants of static group regions *)

typ1:
| t = typ0
    { t }
| typ0 ARROW typ1
    {}

typ2:
| t = typ1
    { t }
| anchored_permission
    {}
(* TEMPORARY
   polymorphic types
   mode constraints as function preconditions and/or as tuple components?
   syntax for anonymous sums?
*)

typ3:
| t = typ2
    { t }
| typ2 STAR typ3 (* conjunction of permissions *)
    {}

(* I considered using COMMA for separating conjunction because this seems
   natural; think of the PRODUCES and CONSUMES clauses in function types.
   However, COMMA is already used to separate multiple arguments in a type
   application, so this means that parentheses will sometimes be necessary
   (e.g. when a conjunction of permissions is used as an argument in a type
   application). Even worse, COMMA is used in the syntax of tuples, and this
   leads to conflicts with tuple types and multi-argument function types.
   So, I give up and use a dedicated symbol, STAR, for conjunction. *)

typ:
  t = typ3
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

(* A concrete data type is necessarily of kind KTYPE. We do not allow defining
   concrete data types of kind KPERM. In principle, we could allow it. I think
   we can live without it (experience will tell). *)

(* ---------------------------------------------------------------------------- *)

(* Terms. *)

(* ---------------------------------------------------------------------------- *)

(* Program units. *)

unit:
  data_type_def*
  EOF
    {}
