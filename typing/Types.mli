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

(** {1 Manipulating types.} *)

(** {2 Building types.} *)

val ty_unit : typ
val ty_tuple : typ list -> typ
val ( @-> ) : typ -> typ -> typ
val ty_bar : typ -> typ -> typ
val ty_app : typ -> typ list -> typ
val ty_equals : var -> typ
val ty_open : var -> typ

(** {2 Binding types} *)

val bind_datacon_parameters :
  env ->
  kind ->
  unresolved_branch list ->
  env * var list * unresolved_branch list

(** {2 Instantiation} *)

val instantiate_type:
  typ -> typ list -> typ
val instantiate_branch:
  unresolved_branch ->
  typ list ->
  unresolved_branch
val find_and_instantiate_branch :
  env ->
  var ->
  Datacon.name ->
  typ list ->
  resolved_branch
val resolve_branch:
  var ->
  unresolved_branch ->
  resolved_branch


(** {2 Folding and unfolding} *)

val flatten_star : env -> typ -> typ list
val fold_star : typ list -> typ
val strip_forall :
  typ ->
  (type_binding * flavor) list * typ
val fold_forall :
  (type_binding * flavor) list ->
  typ -> typ
val fold_exists : (type_binding * flavor) list -> typ -> typ
val expand_if_one_branch : env -> typ -> typ


(* -------------------------------------------------------------------------- *)

(** {1 Type traversals} *)

(** [collect t] syntactically separates [t] into a structural part and a
 * permission part, i.e. it extracts all the permissions hidden inside [t] and
 * returns them as a separate list. *)
val collect : typ -> typ * typ list

(** Mark all type variables reachable from a type, including via the
    ambient permissions. *)
val mark_reachable : env -> typ -> env


(* -------------------------------------------------------------------------- *)

(** {1 Dealing with variables} *)

(** {2 Various getters} *)

val get_location : env -> var -> location
val get_adopts_clause :
  env -> var -> typ
val get_branches :
  env -> var -> unresolved_branch list
val get_arity : env -> var -> int
val get_kind_for_type : env -> typ -> kind
val branches_for_datacon :
  env ->
  resolved_datacon ->
  unresolved_branch list
val branches_for_branch: env -> resolved_branch -> unresolved_branch list
val branch_for_datacon: env -> resolved_datacon -> unresolved_branch
val fields_for_datacon: env -> resolved_datacon -> Field.name list
val flavor_for_branch: env -> resolved_branch -> DataTypeFlavor.flavor

(** Get the variance of the i-th parameter of a data type. *)
val variance : env -> var -> int -> variance

(** {2 Inspecting} *)
val is_tyapp : typ -> (var * typ list) option
val is_abbrev: env -> var -> bool
val is_term : env -> var -> bool
val is_perm : env -> var -> bool
val is_type : env -> var -> bool
val is_user : name -> bool


(* -------------------------------------------------------------------------- *)

(** {1 Miscellaneous} *)

val fresh_auto_name : string -> name
val find_type_by_name :
  env -> ?mname:string -> string -> typ
val make_datacon_letters :
  env ->
  kind ->
  bool ->
  env * var list

(** Our not-so-pretty printer for types. *)
module TypePrinter :
  sig
    val pdoc : Buffer.t -> ('env -> MzPprint.document) * 'env -> unit
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
    val print_exports : env * Module.name -> PPrintEngine.document
    val pexports : Buffer.t -> env * Module.name -> unit
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
    val print_unresolved_branch :
      env ->
      TypeCore.unresolved_branch ->
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
