(** This module defines the abstract syntax of the surface language. *)

(* In principle, very little desugaring is performed on the fly by the
   parser. *)

(* ---------------------------------------------------------------------------- *)

(* Kinds. *)

(* Arrow kinds are not accessible to the user. They are used internally:
   a user-defined algebraic data type constructor receives an arrow kind.
   Thus, even internally, we only use first-order kinds (that is, the
   left-hand argument of an arrow kind is never itself an arrow kind). *)

type kind =
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

(* A small helper function that transforms
 * [κ₁ → ... → κₙ → κ₀] into [[κ₁; ...; κₙ], κ₀] *)
let flatten_kind kind =
  let rec flatten_kind acc = function
    | KArrow (k1, k2) ->
        flatten_kind (k1 :: acc) k2
    | _ as k ->
        acc, k
  in
  let acc, k = flatten_kind [] kind in
  k, List.rev acc


(* ---------------------------------------------------------------------------- *)

(* Types and permissions. *)

type type_binding =
    Variable.name * kind

type consumes_annotation =
  | Consumes
  | ConsumesAndProduces

type typ =
  | TyTuple of tuple_type_component list
  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TyVar of Variable.name
  | TyConcreteUnfolded of data_type_def_branch
  | TySingleton of typ
  | TyApp of typ * typ
  | TyArrow of typ * typ
  | TyForall of type_binding * typ
  | TyAnchoredPermission of typ * typ
  | TyStar of typ * typ

and tuple_type_component =
    consumes_annotation * tuple_type_component_aux

and tuple_type_component_aux =
  | TyTupleComponentValue of Variable.name option * typ
  | TyTupleComponentPermission of typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of anchored_permission
  | FieldPermission of typ

and anchored_permission =
    Variable.name * typ

(* ---------------------------------------------------------------------------- *)

(* Algebraic data type definitions. *)

type data_type_def_lhs =
    Variable.name * type_binding list

type data_type_def_rhs =
    data_type_def_branch list

type data_type_flag = Exclusive | Duplicable

type data_type_def =
    data_type_flag * data_type_def_lhs * data_type_def_rhs

(* A data type group is a group of mutually recursive data type definitions. *)

type data_type_group =
    data_type_def list

