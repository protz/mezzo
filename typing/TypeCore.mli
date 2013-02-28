(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

(** This module defines the syntax of types, as manipulated by the
   type-checker. *)


(** {1 Various useful modules} *)

module DataconMap: MzMap.S with type key = Module.name * Datacon.name
module Field: module type of Variable with type name = SurfaceSyntax.Field.name

(* -------------------------------------------------------------------------- *)


(** {1 The definition of types} *)


(** {2 Auxiliary definitions} *)

(** Types have kinds. *)
type kind = SurfaceSyntax.kind =
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

(** The type of user-generated or auto-generated names. *)
type name = User of Module.name * Variable.name | Auto of Variable.name

(** A type binding defines a type variable bound in a type. *)
and type_binding = name * kind * location

(** Our locations are made up of ranges. *)
and location = Lexing.position * Lexing.position

(** A type binding can be either user-provided, through a universal
 * quantification for instance, or auto-generated, by the desugaring pass for
 * instance. *)
type flavor = SurfaceSyntax.binding_flavor =
  | CanInstantiate
  | CannotInstantiate

(** In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)
type db_index =
  int

(** We adopt a locally nameless style; therefore, variables can be opened.
 * This is the type of open variales; it's abstract, because we provide a set
 * of wrappers and want to prevent mistakes in client code. *)
type var


(** {2 The type of types} *)

(** A field in a data type *)
type data_field_def =
  | FieldValue of (Field.name * typ)
  | FieldPermission of typ

(** The type of types. *)
and typ =
    (** Special type constants. *)
  | TyUnknown
  | TyDynamic

    (** We adopt a locally nameless style. Local names are [TyBound]s, global
     * names are [TyOpen]. *)
  | TyBound of db_index
  | TyOpen of var

    (** Quantification and type application. *)
  | TyForall of (type_binding * flavor) * typ
  | TyExists of type_binding * typ
  | TyApp of typ * typ list

    (** Structural types. *)
  | TyTuple of typ list
  | TyConcreteUnfolded of resolved_datacon * data_field_def list * typ
      (** [typ] is for the type of the adoptees; initially it's bottom and then
       * it gets instantiated to something more precise. *)

    (** Singleton types. *)
  | TySingleton of typ

    (** Function types. *)
  | TyArrow of typ * typ

    (** The bar *)
  | TyBar of typ * typ

    (** Permissions. *)
  | TyAnchoredPermission of typ * typ
  | TyEmpty
  | TyStar of typ * typ

    (** Constraint *)
  | TyAnd of duplicity_constraint list * typ
  | TyImply of duplicity_constraint list * typ

(** Since data constructors are now properly scoped, they are resolved, that is,
 * they are either attached to a point, or a De Bruijn index, which will later
 * resolve to a point when we open the corresponding type definition. That way,
 * we can easily jump from a data constructor to the corresponding type
 * definition. *)
and resolved_datacon = typ * Datacon.name

and duplicity_constraint = SurfaceSyntax.data_type_flag * typ


(** {2 Type definitions} *)

(** Our data constructors have the standard variance. *)
type variance = SurfaceSyntax.variance = Invariant | Covariant | Contravariant | Bivariant

type data_type_def_branch =
    Datacon.name * data_field_def list

type adopts_clause =
  (* option here because not all concrete types adopt someone *)
  typ option

type data_type_def =
  data_type_def_branch list

type type_def =
  (* option here because abstract types do not have a definition *)
    (SurfaceSyntax.data_type_flag * data_type_def * adopts_clause) option
  * variance list

type data_type_group =
  (Variable.name * location * type_def * fact * kind) list


(** {2 Facts} *)

(** A fact refers to any type variable available in scope; the first few facts
 * refer to toplevel data types, and the following facts refer to type variables
 * introduced in the scope, because, for instance, we went through a binder in a
 * function type.
 *
 * The [Fuzzy] case is used when we are inferring facts for a top-level data
 * type; we need to introduce the data type's parameters in the environment, but
 * the correponding facts are evolving as we work through our analysis. The
 * integer tells the number of the parameter. *)
and fact = Exclusive | Duplicable of bitmap | Affine | Fuzzy of int

(** The 0-th element is the first parameter of the type, and the value is true if
  * it has to be duplicable for the type to be duplicable. *)
and bitmap = bool array


(* ---------------------------------------------------------------------------- *)


(** {1 Program-wide environment} *)

(** This is the environment that we use throughout Mezzo. *)
type env

(** The empty environment. *)
val empty_env : env

(** Refresh the location of an environment. *)
val locate : env -> location -> env

(** Get the current location in the environment. *)
val location: env -> location

(** Get the current module name. *)
val module_name: env -> Module.name

(** Set the current module name. *)
val set_module_name: env -> Module.name -> env

(** Is the current environment inconsistent? *)
val is_inconsistent: env -> bool

(** Mark the environment as being inconsistent. *)
val mark_inconsistent: env -> env

(* ---------------------------------------------------------------------------- *)


(** {1 Flexible variables} *)

(** A client of this module, in order to properly deal with flexible variables,
 * must use the wrappers below. *)

(** Is this variable a flexible type variable or not? *)
val is_flexible: env -> var -> bool

(** [instantiate env var t] tries to instantiate the flexible variable [var]
 * with [t]. However, because of various reasons (e.g. levels) this
 * instantiation may or may not be possible directly. *)
val instantiate_flexible: env -> var -> typ -> env option

(** Make sure we're dealing with the real representation of a variable. Any
 * function wishing to examine either a type or a variable should call these two
 * functions; then, whenever they encounter a [TyOpen], they need not worry
 * about it having a structure (because it won't). *)
val modulo_flex_v: env -> var -> typ
val modulo_flex: env -> typ -> typ

(** [import_flex_instanciations env sub_env] brings into [env] all the flexible
 * variable instanciations that happened in [sub_env] without modifying the rest
 * of [env]. *)
val import_flex_instanciations: env -> env -> env


(** {2 Low-level operations} *)

(** Are these two variables the same? This is a low-level operation and you
 * probably want to use [equal] instead. *)
val same: env -> var -> var -> bool

(** Merge two variables while keeping the information about the left one. You
 * must make sure that both variables have been run through [modulo_flex_v]
 * first. This is a low-level operation and you probably want to use
 * {!Permissions.unify} instead. *)
val merge_left: env -> var -> var -> env option

(** Get the list of permissions that are floating in this environment. *)
val get_floating_permissions: env -> typ list

(** Set the list of permissions that are floating in this environment. *)
val set_floating_permissions: env -> typ list -> env

(* ---------------------------------------------------------------------------- *)


(** {1 Playing with variables} *)

(** Get the names associated to a variable. *)
val get_names : env -> var -> name list

(** Get the kind of any given variable. *)
val get_kind : env -> var -> kind

(** Get a fact *)
val get_fact: env -> var -> fact

(** Get the locations *)
val get_locations: env -> var -> location list

(** Get the definition, if any. *)
val get_definition: env -> var -> type_def option

(** {2 Low-level variable manipulation functions.} *)

val add_location: env -> var -> location -> env

(** {2 Low-level permissions manipulation functions.} *)

(** If you're considering playing with the list of permissions available for a
 * given variable, you should consider using {!Permissions.add} and
 * {!Permissions.sub} instead of these low-level, potentially dangerous
 * functions. *)

(** Get the permissions of a term variable. *)
val get_permissions : env -> var -> typ list

(** Set the permissions of a term variable. *)
val set_permissions : env -> var -> typ list -> env

(** Reset the permissions of a term variable. *)
val reset_permissions : env -> var -> env

(** {2 Low-level setters} *)

(** These functions should only be used during the very first few stages of
 * type-checking. *)

(** Set a fact *)
val set_fact: env -> var -> fact -> env

(** Update a definition. This asserts that there used to be a definition before. *)
val update_definition: env -> var -> (type_def -> type_def) -> env

(** Set a definition. This asserts that there was no definition before. *)
val set_definition: env -> var -> type_def -> env

(* ---------------------------------------------------------------------------- *)


(** {1 Fun with sub-environments} *)

exception UnboundPoint

(** [clean env sub_env t] tries to clean up [t], found in [sub_env], so that it
 * makes sense in [env], and throws [UnboundPoint] otherwise *)
val clean: env -> env -> typ -> typ

(** [equal env t1 t2] tells whether [t1] and [t2] can be determined to be equal
 * in environment [env]; it raises [UnboundPoint] is any of these two types
 * doesn't make sense in [env]. *)
val equal: env -> typ -> typ -> bool

(** Equality function on resolved data constructors. *)
val resolved_datacons_equal: env -> resolved_datacon -> resolved_datacon -> bool

(* ---------------------------------------------------------------------------- *)


(** {1 Binding} *)

(** Bind a rigid type variable. *)
val bind_rigid: env -> type_binding -> env * var

(** Bind a flexible type variable. *)
val bind_flexible: env -> type_binding -> env * var

(* ---------------------------------------------------------------------------- *)


(** {1 Exports} *)

(** [get_exports env mname] lists the names exported by module [mname] in [env].
 * [mname] can be either the current module name, or some other module name. *)
val get_exports: env -> Module.name -> (Variable.name * kind * var) list

(* [point_by_name env ?mname x] finds name [x] as exported by module [mname]
 * (default: [module_name env]) in [env]. *)
val point_by_name: env -> ?mname:Module.name -> Variable.name -> var

(* ---------------------------------------------------------------------------- *)


(** {1 Iterating on the bindings} *)

(** We provide a set of fold/map operations on variables defined in the
 * environment. Existential variables are not folded over, as they only serve as
 * placeholders; only rigid variables are consider when performing the various
 * [fold] operations.
 *
 * Of course, we only fold over variables that have been opened in the current
 * environment. *)

(** Fold over all opened types definitions. *)
val fold_definitions: env -> ('acc -> var -> type_def -> 'acc) -> 'acc -> 'acc

(** Fold over all opened terms, providing the corresponding [var] and
 * permissions. *)
val fold_terms: env -> ('acc -> var -> typ list -> 'acc) -> 'acc -> 'acc

(** General fold operation. *)
val fold: env -> ('acc -> var -> 'acc) -> 'acc -> 'acc

(** General map operation. *)
val map: env -> (var -> 'a) -> 'a list

(* ---------------------------------------------------------------------------- *)


(** {1 Marks} *)

val is_marked: env -> var -> bool
val mark: env -> var -> env
val refresh_mark: env -> env

(** This module provides a clean way to map a variable to any given piece of
 * data. Beware, however, that this module only works with rigid variables (it's
 * unclear what it should do for flexible variables), so it's up to the client
 * to properly run {!is_flexible} beforehand. *)
module VarMap: MzMap.S with type key = var


(**/**)

(** References are assigned to by other modules after the type printers have
 * been set up. Other [internal_] functions are for debugging, as they break the
 * abstraction barriers in quite amazing ways. *)
val internal_ptype : (Buffer.t -> env * typ -> unit) ref
val internal_pnames : (Buffer.t -> env * name list -> unit) ref
val internal_ppermissions : (Buffer.t -> env -> unit) ref
val internal_pfact : (Buffer.t -> fact -> unit) ref
val internal_pflexlist: (Buffer.t -> env -> unit)
val internal_uniqvarid: env -> var -> int
val internal_checklevel: env -> typ -> unit
val internal_wasflexible: var -> bool
