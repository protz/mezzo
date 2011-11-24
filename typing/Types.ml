(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are identifiers. Here, variables are
   represented as de Bruijn indices. We keep an identifier at each binding
   site as a pretty-printing hint. *)

type index =
    int

type type_binding =
    SurfaceSyntax.type_binding

type datacon =
    SurfaceSyntax.datacon

(* The annotations [Consumes] and [ConsumesAndProduces] that appear in the
   surface syntax are desugared. They do not appear at this level. *)

(* In the surface syntax, tuple types can bind names for their components.
   Here, this is desugared using singleton types, universal quantification,
   and existential quantification. Tuple type components are now anonymous. *)

type typ =
  | TyTuple of tuple_type_component list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of index
  | TyConcreteUnfolded of data_type_def_branch
  | TySingleton of typ
  | TyApp of typ * typ
  | TyArrow of typ * typ
  | TyForall of type_binding * typ
  | TyExists of type_binding * typ
  | TyAnchoredPermission of typ * typ
  | TyStar of typ * typ

and tuple_type_component =
  | TyTupleComponentValue of typ
  | TyTupleComponentPermission of typ

and data_type_def_branch =
    datacon * data_field_def list

and data_field_def =
  | FieldValue of anchored_permission
  | FieldPermission of typ

and anchored_permission =
    index * typ

