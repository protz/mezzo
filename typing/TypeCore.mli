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

open Kind

(** This module defines the syntax of types, as manipulated by the
   type-checker. *)


(** {1 Various useful modules} *)

module DataconMap: MzMap.S with type key = Module.name * Datacon.name
module Field: module type of Variable with type name = SurfaceSyntax.Field.name

(* -------------------------------------------------------------------------- *)


(** {1 The definition of types} *)


(** {2 Auxiliary definitions} *)

(** The type of user-generated or auto-generated names. *)
type name = User of Module.name * Variable.name | Auto of Variable.name

(** Our locations are made up of ranges. *)
type location = Lexing.position * Lexing.position

(** A type binding defines a type variable bound in a type. *)
type type_binding = name * kind * location

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
  | TyExists of (type_binding * flavor) * typ
  | TyApp of typ * typ list

    (** Structural types. *)
  | TyTuple of typ list
  | TyConcrete of resolved_branch

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
  | TyAnd of mode_constraint * typ

(** Since data constructors are now properly scoped, they are resolved, that is,
 * they are either attached to a point, or a De Bruijn index, which will later
 * resolve to a point when we open the corresponding type definition. That way,
 * we can easily jump from a data constructor to the corresponding type
 * definition. *)
and resolved_datacon = typ * Datacon.name

and mode_constraint = Mode.mode * typ


(** {2 Type definitions} *)

and ('flavor, 'datacon) data_type_def_branch = {
  branch_flavor: 'flavor; (** {!DataTypeFlavor.flavor} or unit *)
  branch_datacon: 'datacon; (** {!Datacon.name} or resolved_datacon *)
  branch_fields: data_field_def list;
    (** The type of the adoptees; initially it's bottom and then
     * it gets instantiated to something less precise. *)
  branch_adopts: typ;
}

and resolved_branch =
    (unit, resolved_datacon) data_type_def_branch

type unresolved_branch =
    (DataTypeFlavor.flavor, Datacon.name) data_type_def_branch

(** Our data constructors have the standard variance. *)
type variance = SurfaceSyntax.variance = Invariant | Covariant | Contravariant | Bivariant

type type_def =
  | Concrete of unresolved_branch list
  | Abstract
  | Abbrev of typ

type data_type = {
  data_name: Variable.name;
  data_location: location;
  data_definition: type_def;
  data_variance: variance list;
  data_fact: Fact.fact;
  data_kind: kind;
}

type data_type_group = {
  group_recursive: SurfaceSyntax.rec_flag;
  group_items: data_type list;
}

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
val is_rigid: env -> var -> bool

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
val get_name : env -> var -> name

(** Get the kind of any given variable. *)
val get_kind : env -> var -> kind

(** Get a fact *)
val get_fact: env -> var -> Fact.fact

(** Get the locations *)
val get_locations: env -> var -> location list

(** Get the definition, if any. *)
val get_definition: env -> var -> type_def option

(** Get the variance, asserting that this variable is that of a type definition. *)
val get_variance : env -> var -> variance list

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
val set_fact: env -> var -> Fact.fact -> env

(** Set a definition. This asserts that there was no definition before. *)
val set_definition: env -> var -> type_def -> variance list -> env

(** Update a definition. This asserts that there used to be a definition before. *)
val update_definition: env -> var -> (type_def -> type_def) -> env

(** Update variance. *)
val update_variance: env -> var -> (variance list -> variance list) -> env

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

(** [point_by_name env ?mname x] finds name [x] as exported by module [mname]
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

(** This is an imperative version of [VarMap], in the form expected by [Fix]. *)
module IVarMap: Fix.IMPERATIVE_MAPS with type key = var

(** {1 Visitors for the internal syntax of types} *)

(** A generic visitor. *)

class virtual ['env, 'result] visitor : object

  (** This method, whose default implementation is the identity,
     allows normalizing a type before inspecting its structure.
     This can be used, for instance, to replace flexible variables
     with the type that they stand for. *)
  method normalize: 'env -> typ -> typ

  (** This method, whose default implementation is the identity,
     can be used to extend the environment when a binding is
     entered. *)
  method extend: 'env -> kind -> 'env

  (** The main visitor method inspects the structure of [ty] and
     dispatches control to the appropriate case method. *)
  method visit: 'env -> typ -> 'result

  (** The case methods have no default implementation. *)
  method virtual tyunknown: 'env -> 'result
  method virtual tydynamic: 'env -> 'result
  method virtual tybound: 'env -> db_index -> 'result
  method virtual tyopen: 'env -> var -> 'result
  method virtual tyforall: 'env -> type_binding -> flavor -> typ -> 'result
  method virtual tyexists: 'env -> type_binding -> flavor -> typ -> 'result
  method virtual tyapp: 'env -> typ -> typ list -> 'result
  method virtual tytuple: 'env -> typ list -> 'result
  method virtual tyconcreteunfolded: 'env -> resolved_branch -> 'result
  method virtual tysingleton: 'env -> typ -> 'result
  method virtual tyarrow: 'env -> typ -> typ -> 'result
  method virtual tybar: 'env -> typ -> typ -> 'result
  method virtual tyanchoredpermission: 'env -> typ -> typ -> 'result
  method virtual tyempty: 'env -> 'result
  method virtual tystar: 'env -> typ -> typ -> 'result
  method virtual tyand: 'env -> mode_constraint -> typ -> 'result

end

(** A [map] specialization of the visitor. *)

class ['env] map : object

  inherit ['env, typ] visitor

  (** The case methods now perform a recursive traversal. *)
  method tyunknown: 'env -> typ
  method tydynamic: 'env -> typ
  method tybound: 'env -> db_index -> typ
  method tyopen: 'env -> var -> typ
  method tyforall: 'env -> type_binding -> flavor -> typ -> typ
  method tyexists: 'env -> type_binding -> flavor -> typ -> typ
  method tyapp: 'env -> typ -> typ list -> typ
  method tytuple: 'env -> typ list -> typ
  method tyconcreteunfolded: 'env -> resolved_branch -> typ
  method tysingleton: 'env -> typ -> typ
  method tyarrow: 'env -> typ -> typ -> typ
  method tybar: 'env -> typ -> typ -> typ
  method tyanchoredpermission: 'env -> typ -> typ -> typ
  method tyempty: 'env -> typ
  method tystar: 'env -> typ -> typ -> typ
  method tyand: 'env -> mode_constraint -> typ -> typ

  (** An auxiliary method for transforming a resolved branch. *)
  method resolved_branch: 'env -> resolved_branch -> resolved_branch
  (** An auxiliary method for transforming a resolved data constructor. *)
  method resolved_datacon: 'env -> resolved_datacon -> resolved_datacon
  (** An auxiliary method for transforming a field. *)
  method field: 'env -> data_field_def -> data_field_def
  (** An auxiliary method for transforming an unresolved branch. *)
  method unresolved_branch: 'env -> unresolved_branch -> unresolved_branch
  (** An auxiliary method for transforming a data type group. *)
  method data_type_group: 'env -> data_type_group -> data_type_group

end

(** An [iter] specialization of the visitor. *)

class ['env] iter : object

  inherit ['env, unit] visitor

  (** The case methods now perform a recursive traversal. *)
  method tyunknown: 'env -> unit
  method tydynamic: 'env -> unit
  method tybound: 'env -> db_index -> unit
  method tyopen: 'env -> var -> unit
  method tyforall: 'env -> type_binding -> flavor -> typ -> unit
  method tyexists: 'env -> type_binding -> flavor -> typ -> unit
  method tyapp: 'env -> typ -> typ list -> unit
  method tytuple: 'env -> typ list -> unit
  method tyconcreteunfolded: 'env -> resolved_branch -> unit
  method tysingleton: 'env -> typ -> unit
  method tyarrow: 'env -> typ -> typ -> unit
  method tybar: 'env -> typ -> typ -> unit
  method tyanchoredpermission: 'env -> typ -> typ -> unit
  method tyempty: 'env -> unit
  method tystar: 'env -> typ -> typ -> unit
  method tyand: 'env -> mode_constraint -> typ -> unit

  (** An auxiliary method for visiting a resolved branch. *)
  method resolved_branch: 'env -> resolved_branch -> unit
  (** An auxiliary method for visiting a resolved data constructor. *)
  method resolved_datacon: 'env -> resolved_datacon -> unit
  (** An auxiliary method for visiting a field. *)
  method field: 'env -> data_field_def -> unit
  (** An auxiliary method for visiting an unresolved branch. *)
  method unresolved_branch: 'env -> unresolved_branch -> unit
  (** An auxiliary method for visiting a data type group. *)
  method data_type_group: 'env -> data_type_group -> unit

end

(**/**)

(** References are assigned to by other modules after the type printers have
 * been set up. Other [internal_] functions are for debugging, as they break the
 * abstraction barriers in quite amazing ways. *)
val internal_ptype : (Buffer.t -> env * typ -> unit) ref
val internal_pnames : (Buffer.t -> env * name list -> unit) ref
val internal_ppermissions : (Buffer.t -> env -> unit) ref
val internal_pfact : (Buffer.t -> Fact.fact -> unit) ref
val internal_pflexlist: (Buffer.t -> env -> unit)
val internal_uniqvarid: env -> var -> int
val internal_checklevel: env -> typ -> unit
val internal_wasflexible: var -> bool

(** The bottom type. *)
val ty_bottom : typ
val is_non_bottom: typ -> typ option
