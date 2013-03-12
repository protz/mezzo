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

(* This module is entirely devoted to computing the variance of type parameters
 * in data types.
 *
 * This module uses [Fix], which we bundle as part of Mezzo. See
 * http://gallium.inria.fr/~fpottier/fix/fix.html.en
 *)

open TypeCore
open Types
open TypeErrors

type t = variance

(* We only have four possible variances:

          invariant
       /             \
  covariant    contravariant
       \             /
          bivariant

*)

(* This computes [a ∪ b]. *)
let lub a b =
  match a, b with
  | Invariant, _
  | _, Invariant ->
      Invariant
  | Bivariant, x
  | x, Bivariant ->
      x
  | x, y ->
      if x = y then
        x
      else
        Invariant
;;

let leq a b = (lub a b) = b;;

(* Variance inversion (e.g. left of an arrow). *)
let (~~) = function
  | Invariant -> Invariant
  | Covariant -> Contravariant
  | Contravariant -> Covariant
  | Bivariant -> Bivariant
;;

(* When variable [a] is used in place of [b] in a type application, this
 * generates a new constraint for [a].
 *
 * For instance, if "foo a" is defined as "Foo { foo: list (a, a) }" and "b"
 * represents the type variable that appears for "list", then the variance of
 * "a" in the definition of "foo" is "b.(variance of a in (a, a))".
 * In our case, covariant. *)
let dot a b =
  match a, b with
  | Invariant, Bivariant ->
      Bivariant
  | Invariant, _ ->
      Invariant
  | Covariant, b ->
      b
  | Contravariant, b ->
      ~~b
  | Bivariant, _ ->
      Bivariant
;;

(* This computes the variance of solver variable [b] in type [t]. [var_for_ith]
 * gives the solver variable associated to the i-th type parameter of a
 * constructor. [env] is needed to compare that two variables are equal (we use
 * points as variables of the [Fix] module). *)
let variance env var_for_ith valuation b t =
  let rec var = function
    | TyUnknown
    | TyDynamic
    | TyBound _
    | TyEmpty ->
        Bivariant

    | TyOpen a ->
        if same env a b then
          Covariant
        else
          Bivariant

    | TyForall (_, t)
    | TyExists (_, t) ->
        var t

    | TyApp (cons, args) ->
        let cons = !!cons in
        let vs = List.mapi (fun i arg ->
          let valuation_a =
            try
              valuation (var_for_ith cons i)
            with Not_found ->
              List.nth (get_variance env cons) i
          in
          dot valuation_a (var arg)
        ) args in
        List.fold_left lub Bivariant vs

    | TyTuple ts ->
        let vs = List.map var ts in
        List.fold_left lub Bivariant vs

    | TyConcreteUnfolded branch ->
        let vs = List.map (function
          | FieldValue (_, t) ->
              var t
          | FieldPermission p ->
              var p
        ) branch.branch_fields in
        let vs = var branch.branch_adopts :: vs in
        List.fold_left lub Bivariant vs

    | TySingleton _ ->
        Bivariant

    | TyArrow (t1, t2) ->
        lub ~~(var t1) (var t2)

    | TyBar (t1, t2)
    | TyStar (t1, t2) ->
        lub (var t1) (var t2)

    | TyAnchoredPermission (_, t2) ->
        var t2

    | TyAnd ((_, t), u)
    | TyImply ((_, t), u) ->
	(* [t] is in invariant position, [u] is in covariant position. *)
	lub
	  (dot Invariant (var t))
	  (var u)
  in
  var t
;;


module P = struct
  type property = t
  let bottom = Bivariant
  let equal = (=)
  let is_maximal = (=) Invariant
end

module Solver = Fix.Make(IVarMap)(P)

let analyze_data_types env points =
  (* Keep the original env fresh, since we're going to throw away most of the
   * work below. *)
  let original_env = env in

  (* Create a sub-enviroment where points have been allocated for each one of
   * the data type parameters. We keep a list of instantiated branches with
   * their corresponding point. *)
  let env, store =
    List.fold_left (fun (env, acc) point ->
      let kind = get_kind env point in
      let definition = get_definition env point in
      match definition with
      | None ->
          Log.error "Only data type definitions here"
      | Some (None, _) ->
          env, acc
      | Some (Some branches, _) ->
          let env, points, instantiated_branches =
            bind_datacon_parameters env kind branches
          in
          env, (point, (points, instantiated_branches)) :: acc
    ) (original_env, []) points
  in

  (* This function is needed inside [variance]. It returns a variable (i.e. a
   * point) that represents the i-th parameter of the given constructor. *)
  let var_for_ith cons i =
    let _, (vars, _) = List.find (fun (cons', _) -> same env cons cons') store in
    List.nth vars i
  in

  (* This computes the rhs for a given variable. *)
  let equations var =
    (* Find which type this variable belongs to. *)
    let _, (_, branches) = List.find (fun (_, (vars, _)) ->
      List.exists (same env var) vars
    ) store in
    (* The equations for a given variable depend on the valuation. (At this
     * stage, you should really, really read the doc for [Fix].) *)
    (fun valuation ->
      let vs = List.map
        (variance env var_for_ith valuation var)
        (List.map (fun branch ->
	  TyConcreteUnfolded { branch with branch_datacon = (TyUnknown, branch.branch_datacon) } (* yuch! *)
	 ) branches)
      in
      List.fold_left lub Bivariant vs
    )
  in

  (* Solve! *)
  let valuation = Solver.lfp equations in

  (* Update the data type definitions. *)
  let original_env = List.fold_left (fun env (cons, (vars, _)) ->
    let variance = List.map valuation vars in
    update_definition env cons (fun (branches, annotated_variance) ->
      if not (List.for_all2 leq variance annotated_variance) then
        raise_error env VarianceAnnotationMismatch;
      branches, variance
    )
  ) original_env store in
  original_env
;;
