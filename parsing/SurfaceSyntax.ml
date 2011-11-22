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

type type_binding =
    identifier * kind

type consumes_annotation =
  | Consumes
  | ConsumesAndProduces

type typ =
  | TyTuple of tuple_type_component list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of identifier
  | TyConcreteUnfolded of data_type_def_branch
  | TySingleton of identifier
  | TyApp of typ * typ
  | TyArrow of typ * typ
  | TyForall of type_binding * typ
  | TyAnchoredPermission of anchored_permission
  | TyStar of typ * typ

and tuple_type_component =
    consumes_annotation * tuple_type_component_aux

and tuple_type_component_aux =
  | TyTupleComponentAnonymousValue of typ
  | TyTupleComponentNamedValue of anchored_permission
  | TyTupleComponentPermission of typ

and data_type_def_branch =
    datacon * data_field_def list

and data_field_def =
  | FieldValue of anchored_permission
  | FieldPermission of typ

and anchored_permission =
    identifier * typ

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_lhs =
    identifier * type_binding list

type data_type_def_rhs =
    data_type_def_branch list

type data_type_def =
    data_type_def_lhs * data_type_def_rhs

(* A data type group is a group of mutually recursive data type definitions. *)

type data_type_group =
    data_type_def list

