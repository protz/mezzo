(* This module defines the abstract syntax of the surface language. *)

(* In principle, very little desugaring is performed on the fly by the
   parser. *)

(* ---------------------------------------------------------------------------- *)

(* Identifiers are (unique) integer codes. *)

type identifier =
    int

type datacon =
    int

(* ---------------------------------------------------------------------------- *)

(* Kinds. *)

type kind =
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

type consumes_annotation =
  | Consumes
  | ConsumesAndProduces

type typ =
  | TyTuple of tuple_type_component list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of identifier
  | TyConcreteUnfolded of datacon * data_field_def list
  | TySingleton of identifier
  | TyApp of typ * typ
  | TyArrow of typ * typ
  | TyAnchoredPermission of anchored_permission
  | TyStar of typ * typ

and tuple_type_component =
    consumes_annotation * tuple_type_component_aux

and tuple_type_component_aux =
  | TyTupleComponentAnonymousValue of typ
  | TyTupleComponentNamedValue of anchored_permission
  | TyTupleComponentPermission of typ

and data_field_def =
  | FieldValue of anchored_permission
  | FieldPermission of typ

and anchored_permission =
    identifier * typ

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type type_binding =
    identifier * kind

type data_type_def_lhs =
    identifier * type_binding list

type data_type_def_branch =
    datacon * data_field_def list

type data_type_def_rhs =
    data_type_def_branch list

type data_type_def =
    data_type_def_lhs * data_type_def_rhs

