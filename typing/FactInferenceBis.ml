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

open TypeCore
open Types

(* TODO rethink the whole thing while sharing code between exclusive and
   duplicable; define lattice *)

let is_exclusive_fact = function
  | Exclusive ->
      true
  | Affine
  | Duplicable _ ->
      false
  | Fuzzy _ ->
      (* TEMPORARY get rid of this case? *)
      assert false

(* A type [t] is exclusive if and only if the permission [x @ t] implies
   the exclusive ownership of the object at address [x]. *)

(* I don't know if we could define what it means for a permission [p] to
   be exclusive. I will assume that when we write [exclusive t], [t] has
   kind [type]. *)

let rec is_exclusive (env : env) (ty : typ) : bool =
  let ty = modulo_flex env ty in
  match ty with

  | TyOpen point ->
      (* When we find a free type variable, we look it up in the environment.
	 We may have a hypothesis about it. *)
      is_exclusive_fact (get_fact env point)

  (* Comments on universal types. *)

  (* A weird type such as ([a] duplicable a => ref int) is logically equivalent
   * to (ref int), hence is exclusive. Similarly, ([a] exclusive a => ref int) is
   * exclusive. And ([a] duplicable a => exclusive a => ref int) is logically
   * equivalent to (ref int), because the type bottom is both exclusive and
   * duplicable. *)

  (* When trying to prove that [a]u is exclusive, we might wish to assume that
     a has fact bottom in the lattice of facts, or equivalently (?), we might
     wish to instantiate a with the type bottom. This is not implemented yet. *)

  (* For the moment, we assume that a is exclusive; this is sound and only very
     marginally incomplete. *)

  | TyForall ((binding, _), t') ->
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var Exclusive in
      is_exclusive env t'

  | TyExists (binding, t') ->
      (* Be conservative: assume that the quantified variable is affine. *)
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var Affine in
      is_exclusive env t'

  | TyApp (cons, _) ->
      is_exclusive_fact (get_fact env !!cons)

  | TyConcreteUnfolded (datacon, _, _) ->
      let flag, _, _ = def_for_datacon env datacon in
      begin match flag with
      | SurfaceSyntax.Exclusive ->
	  true
      | SurfaceSyntax.Duplicable ->
	  false
      end

  (* Comments about constraints. *)

  (* The existential type {a} (exclusive a /\ a) is exclusive.
     Similarly, {a} (duplicable a /\ a) is duplicable. When we
     find a [TyAnd] node, we should be able to assume that the
     constraint holds before continuing. Technically, the type
     {a} (a, (duplicable a /\ a)) is duplicable too; in order
     to be able to prove this, we might need to defer our answer
     at variables. *)

  | TyAnd (_, ty) ->
      (* TEMPORARY too conservative: the constraints are ignored. *)
      is_exclusive env ty

  (* The type c => t is equivalent to t if the constraint holds,
     and is equivalent to unknown otherwise. Thus, this type is
     exclusive only if c holds and t is exclusive. However, we
     do not know if c holds, and the question does not really
     make sense, as it makes the system non-monotonic. Consider
     the following recursive abbreviation:

     alias t = (duplicable t => ref int)

     If t is duplicable, then t is logically equivalent to ref
     int, so t is exclusive. If t is exclusive, then t is not
     duplicable (? presumably t is not bottom), so t is logically
     equivalent to unknown, so t is duplicable. This is completely
     inconsistent!

     In order to avoid these problems, it seems reasonable to say
     that a type of the form c => t is never exclusive, period. *)

  | TyImply _ ->
      false

  | TyBar (ty, _) ->
      is_exclusive env ty

  | TyUnknown
  | TyDynamic
  | TyTuple _
  | TySingleton _
  | TyArrow _
      -> false

  | TyBound _ ->
      Log.error "There should be no bound variables here."

  | TyAnchoredPermission _
  | TyEmpty
  | TyStar _ ->
      Log.error "is_exclusive is defined only at kind type."
      (* TEMPORARY make sure that the kind checking algorithm agrees with this *)


let rec is_duplicable (env : env) (ty : typ) : bool (* TODO lattice point instead of bool *) =
  let ty = modulo_flex env ty in
  match ty with

  | TyOpen _ ->
      (* TODO *)
      (* if free variable: look up fact in environment *)
      (* if parameter of current def: return lattice point for this parameter *)
      (* must be able to identify its number *)
      assert false

  | TyApp (cons, args) ->
      (* TODO should not use [get_fact env], but should use a valuation
	 received as an argument *)
      begin match get_fact env !!cons with
      | Fuzzy _ ->
	  assert false (* cannot happen *)
      | Exclusive
      | Affine ->
	  false
      | Duplicable cons_bitmap ->
	  (* For each argument of the type application... *)
	  List.iteri (fun i ti ->
	    (* The type at [level] may request its [i]-th parameter to be
	     * duplicable. *)
	    if cons_bitmap.(i) then begin
	      (* The answer is yes: the [i]-th parameter for the type
	       * application is [ti] and it has to be duplicable for the
	       * type at [level] to be duplicable too. *)
	      let (_ : bool) = is_duplicable env ti in
	      ()
	    end else begin
	      (* The answer is no: there are no constraints on [ti]. *)
	      ()
	    end
	  ) args;
	  false (* TODO *)
      end

  | TyForall ((binding, _), t') ->
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var (Duplicable [||]) in
      is_duplicable env t'

  | TyExists (binding, t') ->
      (* Be conservative: assume that the quantified variable is affine. *)
      let env, t', var = bind_rigid_in_type env binding t' in
      let env = set_fact env var Affine in
      is_duplicable env t'

  | TyTuple tys ->
      List.fold_left (fun accu ty -> accu && is_duplicable env ty) true tys

  | TyConcreteUnfolded (datacon, fields, _) ->
      let flag, _, _ = def_for_datacon env datacon in
      begin match flag with
      | SurfaceSyntax.Duplicable ->
	  List.fold_left (fun accu field -> accu && is_duplicable_field env field) true fields
      | SurfaceSyntax.Exclusive ->
	  true
      end

  | TyAnd (_, ty) ->
      (* TEMPORARY too conservative: the constraints are ignored. *)
      is_duplicable env ty

  (* The type c => t is logically equivalent to the type t if c holds
     and is logically equivalent to the type unknown otherwise. Because
     unknown is duplicable, the type c => t is duplicable if and only if
     c implies that t is duplicable. Thus, we may assume that c holds,
     just as in the case of TyAnd! Yet, TyAnd and TyImply are still
     different, as the former can be hoisted out, whereas the latter
     cannot. *)

  | TyImply _ ->
      (* TEMPORARY too conservative: the constraints are ignored. *)
      is_duplicable env ty

  | TyBar (ty1, ty2)
  | TyStar (ty1, ty2) ->
      is_duplicable env ty1 && is_duplicable env ty2

  | TyUnknown
  | TyDynamic
  | TyEmpty
  | TySingleton _
  | TyArrow _
      -> true

  | TyAnchoredPermission (_, ty) ->
      is_duplicable env ty

  | TyBound _ ->
      Log.error "There should be no bound variables here."

and is_duplicable_field env = function
  | FieldValue (_, ty)
  | FieldPermission ty ->
      is_duplicable env ty

and conjunction cs =
  List.fold_left (fun accu c -> accu && c) true cs

