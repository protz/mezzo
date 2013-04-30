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

(* This module implements a well-kindedness check for the types of the surface
   language. It also offers the necessary building blocks for resolving names
   (i.e. determining which definition each variable and data constructor refers
   to) and translating types and expressions down to the internal syntax. *)

open Kind
open SurfaceSyntax

(* ---------------------------------------------------------------------------- *)

(* An environment maintains a mapping of external variable names to internal
   objects, represented by the type [var]. A [var] is either a local name,
   represented as de Bruijn index, or a non-local name, represented in some
   other way. Typically, when checking a compilation unit, the names defined
   within this compilation unit are translated to local names, whereas the
   names defined in other units that this unit depends on are translated to
   non-local names. *)

type 'v var =
       Local of int
  | NonLocal of 'v

type 'v env

(* ---------------------------------------------------------------------------- *)

(* Errors. *)

(** A [KindError] exception carries a function that displays an error message. *)
exception KindError of (Buffer.t -> unit -> unit)

(* TEMPORARY try not to publish any of the functions that raise errors? *)
val implication_only_on_arrow: 'v env -> 'a
val illegal_consumes: 'v env -> 'a

(* ---------------------------------------------------------------------------- *)

(* Building environments. *)

(** An empty environment. *)
val empty: Module.name -> 'v env

(** A so-called initial environment can be constructed by populating an empty
    environment with qualified names of variables and data constructors. They
    represent names that have been defined in a module other than the current
    module. *)
val initial:
  Module.name ->
  (Module.name * Variable.name * kind * 'v) list ->
  (Module.name * 'v * int * Datacon.name * Field.name list) list ->
  'v env

(* ---------------------------------------------------------------------------- *)

(* Extracting information out of an environment. *)

(** [module_name env] is the name of the current module. *)
val module_name: 'v env -> Module.name

(** [location env] is the current location in the source code. *)
val location: 'v env -> location

(** [find_variable env x] looks up the possibly-qualified variable [x]
    in the environment [env]. *)
val find_variable: 'v env -> Variable.name maybe_qualified -> 'v var

(** [resolve_datacon env dref] looks up the possibly-qualified data constructor
    [dref.datacon_unresolved] in the environment [env]. It updates [dref] in
    place with a [datacon_info] component. It returns a pair of the type with
    which this data constructor is associated and the unqualified name of this
    data constructor. *)
val resolve_datacon: 'v env -> datacon_reference -> 'v var * Datacon.name

(* ---------------------------------------------------------------------------- *)

(* Extending an environment. *)

(** [locate env loc] updates [env] with the location [loc]. *)
val locate: 'v env -> location -> 'v env

(** [extend env bindings] iterates over the list [bindings], from left to
    right, and for each binding of the form [(x, kind, loc)], it extends
    the environment by binding the unqualified variable [x] to a new local
    name whose kind is [kind]. *)
val extend: 'v env -> type_binding list -> 'v env

(** [bind_nonlocal env (x, kind, v)] binds the unqualified variable [x] to the
    non-local name [v], whose kind is [kind]. *)
val bind_nonlocal: 'v env -> Variable.name * kind * 'v -> 'v env

(** [dissolve env m] has the effect of introducing a new binding of [x]
    for every existing binding of [m::x]. This concerns both variables and
    data constructors. *)
val dissolve: 'v env -> Module.name -> 'v env

(** [bindings_data_group_types group] returns a list of bindings for the types
    of the data group. *)
val bindings_data_group_types: data_type_def list -> type_binding list

(** [bind_data_group_datacons env group] extends the environment with bindings
    for the data constructors of the data group. It must be called after the
    environment has been extended with bindings for the types. *)
val bind_data_group_datacons: 'v env -> data_type_def list -> 'v env

(* ---------------------------------------------------------------------------- *)

(* Functions for obtaining the bindings introduced by a pattern or by a type
   (interpreted as a pattern). *)

(** [bv p] returns the names bound by the pattern [p], in left-to-right order.
    The order matters -- the de Bruijn numbering convention relies on it. *)
val bv: pattern -> type_binding list

(** [names ty] returns a list of the names introduced by the type [ty], via
    [TyNameIntro] forms. The list is returned in left-to-right order, as
    above. [names] is in fact implemented via a call to [bv]. *)
val names: typ -> type_binding list

(* ---------------------------------------------------------------------------- *)

(* Kind-checking functions. *)

(** [infer_reset env ty] returns the kind of the type [ty]. *)
val infer_reset: 'v env -> typ -> kind

(** [check_implementation env i] checks that the implementation file [i] is
    well-formed, i.e. all names are properly bound and all types are
    well-kinded. *)
val check_implementation: 'v env -> implementation -> unit

(** [check_implementation env i] checks that the interface file [i] is
    well-formed, i.e. all names are properly bound and all types are
    well-kinded. *)
val check_interface: 'v env -> interface -> unit

