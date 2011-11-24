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

(* TEMPORARY we need a notion of type equality, or subtyping, that deals with
   quantifiers in a transparent way -- especially the quantifiers introduced
   by the translation of named tuple components down to this kernel syntax.
   E.g. we need (the translation of) [t] to be interconvertible with (the
   translation of) [(x: t)], which is [exists x :: term. (=x, permission x: t)].
   Hmm, tricky, tricky. Do we really want to go this way? *)

(* TEMPORARY also, subtyping must take into account the AC axioms for TyStar,
   the fact that TyEmpty is neutral for TyStar, and (perhaps) the fact that
   duplicable permissions are idempotent for TyStar. Tricky, tricky. *)

(* TEMPORARY also, subtyping must take into account the fact that tuple
   components which are anonymous permissions can freely move around
   within a tuple. Hmm, hmm. *)

(* TEMPORARY perhaps we could completely avoid the need for subtyping
   (and solve all three problems above) by working with explicit
   eta-expansions instead. This requires thought! *)

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
  (* TEMPORARY TyShift constructor for lazy shifting of de Bruijn indices? *)

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

(* ---------------------------------------------------------------------------- *)

(* Fun with de Bruijn indices. *)

