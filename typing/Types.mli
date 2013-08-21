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

(** This module provides a variety of functions for dealing with types, mostly
 * built on top of {!DeBruijn} and {!TypeCore}. *)

open Kind
open TypeCore

(* -------------------------------------------------------------------------- *)

(** {1 Convenient combinators.} *)

(** {2 Dealing with triples.} *)

val fst3 : 'a * 'b * 'c -> 'a
val snd3 : 'a * 'b * 'c -> 'b
val thd3 : 'a * 'b * 'c -> 'c

(** {2 Operators} *)

(** Asserts that this type is actually a [TyOpen]. *)
val ( !! ) : typ -> var

(** Asserts that this type is actually a [TySingleton (TyOpen ...)]. *)
val ( !!= ) : typ -> var

(** This is {!Lazy.force}. *)
val ( !* ) : 'a Lazy.t -> 'a

(** [bind] for the option monad. *)
val ( >>= ) : 'a option -> ('a -> 'b option) -> 'b option

(** [either] operator for the option monad *)
val ( ||| ) : 'a option -> 'a option -> 'a option

(** The standard implication connector, with the right associativity. *)
val ( ^=> ) : bool -> bool -> bool

(** The pipe operator. *)
val ( |> ) : 'a -> ('a -> 'b) -> 'b


(* -------------------------------------------------------------------------- *)

(** {1 Normalizing types.} *)

(** These functions, when combined with {!TypeCore.modulo_flex}, allow one to
 * manipulate a "canonical" representation of a type, where permissions have
 * been stripped out and unfoldings have been performed. One will still want to
 * use {!Permissions.open_all_rigid_in}, though. *)

(** [expand_if_one_branch env t] expands [t] when [t] is either a type
 * abbreviation, or a data type with one branch. *)
val expand_if_one_branch : env -> typ -> typ

(** [collect t] syntactically separates [t] into a structural part and a
 * permission part, i.e. it extracts all the permissions hidden inside [t] and
 * returns them as a separate list. *)
val collect : typ -> typ * typ list


(* -------------------------------------------------------------------------- *)

(** {1 Branches.} *)

(** Data types have branches. A branch has a _parent_ data type. [branch] is the
 * type that represents an actual branch under a [TyConcrete]; a branch in a
 * data type definition can be any type, most functions return a [typ]. *)

(** Given a [branch], get all the other branches of the parent type. *)
val branches_for_branch: env -> branch -> typ list

(** Given a [resolved_datacon], get all the other branches of the parent type. *)
val branches_for_datacon: env -> resolved_datacon -> typ list

(** Given a [resolved_datacon], get the corresponding branch. *)
val branch_for_datacon: env -> resolved_datacon -> typ

(** Given a [resolved_datacon], get all its fields. *)
val fields_for_datacon: env -> resolved_datacon -> Field.name list

(** Given a [resolved_datacon], get its flavor. *)
val flavor_for_datacon: env -> resolved_datacon -> DataTypeFlavor.flavor


(* -------------------------------------------------------------------------- *)

(** {1 Manipulating types.} *)


(** {2 Building types.} *)

(** We provide a set of wrappers to easily build types. These often perform
 * extra checks. *)

(** Shortcut for the empty tuple [TyTuple []]. *)
val ty_unit : typ

(** A tuple. *)
val ty_tuple : typ list -> typ

(** An arrow. The operator has the right associativity. *)
val ( @-> ) : typ -> typ -> typ

(** [ty_bar t1 t2] is [TyBar (t1, t2)] is [t2] is not [TyEmpty], [t1] otherwise. *)
val ty_bar : typ -> typ -> typ

(** [ty_app t ts] is [TyApp (t, ts)] if [List.length ts > 0], [t] otherwise. *)
val ty_app : typ -> typ list -> typ

(** Shortcut for [TySingleton (TyOpen _)]. *)
val ty_equals : var -> typ

(** A open variable. *)
val ty_open : var -> typ


(** {2 Inspecting} *)

(** We provide a set of wrappers to inspect types. *)

(** Works with either [TyOpen] or [TyApp]. *)
val is_tyapp : typ -> (var * typ list) option

(** Calls [modulo_flex] and [expand_if_one_branch] before determining whether
 * it's a [TyStar] or not. *)
val is_star : env -> typ -> bool

(** Is this a concrete type? *)
val is_concrete : typ -> bool

(** If you know this is a concrete type, extract the [branch]. *)
val assert_concrete : typ -> branch

(** Is this an open variable? *)
val is_tyopen : typ -> bool

(** Determines whether a variable corresponds to a type abbreviation definition. *)
val is_abbrev: env -> var -> bool

(** Has this variable kind [term]? *)
val is_term : env -> var -> bool

(** Has this variable kind [perm]? *)
val is_perm : env -> var -> bool

(** Has this variable kind [type]? *)
val is_type : env -> var -> bool

(** Is this name user-provided? *)
val is_user : name -> bool


(** {2 Folding and flattening} *)

(** Transform a [TyStar] into a flat list of permissions. This function performs
 * quite a bit of work to make sure there are no nested permissions: it calls
 * [modulo_flex] and [expand_if_one_branch] and extract all permissions nested
 * in [t] when it encounters [x @ t]. *)
val flatten_star : env -> typ -> typ list

(** This function has a special case to make sure it doesn't introduce useless
 * [TyEmpty]s. *)
val fold_star : typ list -> typ

(** Fold a type under a series of universal bindings. *)
val fold_forall : (type_binding * flavor) list -> typ -> typ

(** Fold a type under a series of existential bindings. *)
val fold_exists : (type_binding * flavor) list -> typ -> typ


(* -------------------------------------------------------------------------- *)

(** {1 Type traversals} *)

(** Mark all type variables reachable from a type, including via the
    ambient permissions. *)
val mark_reachable : env -> typ -> env


(* -------------------------------------------------------------------------- *)

(** {1 Binding and instantiating} *)

(** {2 Binding types} *)

(** [bind_datacon_parameters env k ts] takes the kind of the parent data type
 * [k], its branches [ts], and introduces open variables that stand for the data
 * type's parameters in all the branches. *)
val bind_datacon_parameters : env -> kind -> typ list -> env * var list * typ list

(** {2 Instantiation} *)

(** [instantiate_type t ts] substitutes the givens types [t0, ..., tn] for
 * [TyBound 0, ... TyBound n] in [t]. *)
val instantiate_type: typ -> typ list -> typ 

(** Find the branch and substitute the data type's parameters in it. *)
val find_and_instantiate_branch : env -> var -> Datacon.name -> typ list -> typ


(* -------------------------------------------------------------------------- *)

(** {1 Miscellaneous} *)

(** {2 Various getters} *)

val get_location : env -> var -> location
val get_adopts_clause : env -> var -> typ
val get_arity : env -> var -> int
val get_kind_for_type : env -> typ -> kind

(** Get the variance of the i-th parameter of a data type. *)
val variance : env -> var -> int -> variance

val fresh_auto_name : string -> name
val make_datacon_letters :
  env ->
  kind ->
  bool ->
  env * var list

(** Our not-so-pretty printer for types. *)
module TypePrinter :
  sig
    val print_var : env -> name -> MzPprint.document
    val pvar : Buffer.t -> env * name -> unit
    val print_datacon : Datacon.name -> MzPprint.document
    val print_field_name : Field.name -> MzPprint.document
    val print_field : SurfaceSyntax.field -> MzPprint.document
    val p_kind : Buffer.t -> kind -> unit
    val print_names :
      env -> name list -> MzPprint.document
    val pnames : Buffer.t -> env * name list -> unit
    val pname : Buffer.t -> env * var -> unit
    val print_quantified :
      env ->
      string ->
      name -> kind -> typ -> MzPprint.document
    val print_point : env -> var -> MzPprint.document
    val print_type : env -> typ -> MzPprint.document
    val print_constraint :
      env ->
      mode_constraint -> MzPprint.document
    val print_data_field_def :
      env -> data_field_def -> MzPprint.document
    val print_branch :
      env ->
      TypeCore.branch ->
      MzPprint.document
    val pfact : Buffer.t -> Fact.fact -> unit
    val print_facts : env -> MzPprint.document
    val print_permission_list :
      env * typ list -> MzPprint.document
    val ppermission_list : Buffer.t -> env * var -> unit
    val print_permissions : env -> MzPprint.document
    val ppermissions : Buffer.t -> env -> unit
    val ptype : Buffer.t -> env * typ -> unit
    val penv : Buffer.t -> env -> unit
    val pconstraint :
      Buffer.t -> env * mode_constraint -> unit
    val print_binders : env -> MzPprint.document
  end
