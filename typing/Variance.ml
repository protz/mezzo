(* This module is entirely devoted to computing the variance of type parameters
 * in data type.
 *
 * This module uses [Fix], which we bundle as part of Mezzo. See
 * http://gallium.inria.fr/~fpottier/fix/fix.html.en
 *)

open Types

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
    | TyVar _
    | TyEmpty ->
        Bivariant

    | TyPoint a ->
        if same env a b then
          Covariant
        else
          Bivariant

    | TyForall (_, t)
    | TyExists (_, t) ->
        var t

    | TyApp _ as t ->
        let cons, args = flatten_tyapp t in
        let vs = List.mapi (fun i arg ->
          let a = var_for_ith !!cons i in
          dot (valuation a) (var arg)
        ) args in
        List.fold_left lub Bivariant vs

    | TyTuple ts ->
        let vs = List.map var ts in
        List.fold_left lub Bivariant vs

    | TyConcreteUnfolded (_, fields, clause) ->
        let vs = List.map (function
          | FieldValue (_, t) ->
              var t
          | FieldPermission p ->
              var p
        ) fields in
        let vs = var clause :: vs in
        List.fold_left lub Bivariant vs

    | TySingleton t ->
        var t

    | TyArrow (t1, t2) ->
        lub ~~(var t1) (var t2)

    | TyBar (t1, t2)
    | TyAnchoredPermission (t1, t2)
    | TyStar (t1, t2) ->
        lub (var t1) (var t2)

    | TyConstraints (constraints, t) ->
        let ts = List.map snd constraints in
        let vs = List.map var (t :: ts) in
        List.fold_left lub Bivariant vs
  in
  var t
;;


module P = struct
  type property = t
  let bottom = Bivariant
  let equal = (=)
  let is_maximal = (=) Invariant
end

module M = struct
  type key = point
  type 'data t = 'data PointMap.t ref
  let create () = ref PointMap.empty
  let clear m = m := PointMap.empty
  let add k v m = m := (PointMap.add k v !m)
  let find k m = PointMap.find k !m
  let iter f m = PointMap.iter f !m
end

module Solver = Fix.Make(M)(P)

let analyze_data_types env =
  (* Keep the original env fresh, since we're going to throw away most of the
   * work below. *)
  let original_env = env in

  (* Create a sub-enviroment where points have been allocated for each one of
   * the data type parameters. We keep a list of instantiated branches with
   * their corresponding point. *)
  let env, store =
    fold_types original_env (fun (env, acc) point { kind; _ } { definition; _ } ->
      match definition with
      | None ->
          Log.error "Only data type definitions here"
      | Some (None, _) ->
          env, acc
      | Some (Some (_flag, branches, clause), _) ->
          let env, points, instantiated_branches, clause =
            bind_datacon_parameters env kind branches clause
          in
          let clause = match clause with Some clause -> clause | None -> ty_bottom in
          (* Keep the clause along with the branches so that [equations] can
           * generate proper concrete types, which will in turn use the clause
           * to generate correct equations. *)
          env, (point, (points, (List.map (fun (x, y) -> x, y, clause) instantiated_branches))) :: acc
    ) (original_env, [])
  in

  (* This function is needed inside [variance]. *)
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
     * stagae, you should really, really read the doc for [Fix].) *)
    (fun valuation ->
      (* The [z] parameter is actually the adopts clause that has been
       * distributed in all the branches so as to give the correct behavior. *)
      let vs = List.map
        (variance env var_for_ith valuation var)
        (List.map (fun (x, y, z) -> TyConcreteUnfolded (x, y, z)) branches)
      in
      List.fold_left lub Bivariant vs
    )
  in

  (* Solve! *)
  let valuation = Solver.lfp equations in

  (* Update the data type definitions. *)
  let original_env = List.fold_left (fun env (cons, (vars, _)) ->
    let variance = List.map valuation vars in
    replace_type env cons (fun binding ->
      let definition =
        match binding.definition with
        | Some ((Some _) as branches, _) ->
            Some (branches, variance)
        | _ ->
            Log.error "Only data type definitions here"
      in
      { binding with definition }
    )
  ) original_env store in
  original_env
;;
