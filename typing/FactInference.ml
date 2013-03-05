module F = FactInferenceBis (* TEMPORARY *)

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

(* ------------------------------------------------------------------------- *)

(* The core of the algorithm. *)

(* The algorithm below can be used in two distinct phases. The first one
 * analyses a given data type definition, so the algorithm is allowed to request
 * that a parameter be duplicable for the whole type to be duplicable. The
 * second one tries to tell whether a given type is duplicable or not later on.
 * *)
type phase = Elaborating of bitmap | Checking


(* The code of this module is written in an imperative style. Therefore, the
 * code may throw an exception to indicate that the type that it is currently
 * analyzing is not duplicable. The type may not be duplicable because:
 * - some sub-part of it is affine,
 * - some sub-part of it is exclusive; if the sub-part is a strict sub-part of
 *   the type (e.g. a tuple component), then the whole type is said to be
 *   affine; if the entire type is exclusive, then we can safely state the whole
 *   type is exclusive.
 * This relies on [duplicables] throwing the right [EExclusive] exception
 * containing the entire type. *)
exception EAffine
exception EExclusive of typ


(* This function performs a reverse-analysis of a type. As it goes, it marks
 * those variables that needs to be duplicable by updating the bitmap contained
 * in [phase]. It may throw [EAffine] if it turns out the type it's
 * currently analyzing is affine. *)
let duplicables
    (env: env) 
    (phase: phase)
    (t: typ): unit =

  (* Ok this algorithm needs to be completely rewritten in a functional style,
   * this is the oldest piece of code in the type-checker ana it's really
   * terrible. *)
  let rec follows_exclusive env t t_parent =
    try
      duplicables env t
    with EExclusive t' when equal env t t' ->
      raise (EExclusive t_parent)

  and duplicables (env: env) (t: typ): unit =
    let t = modulo_flex env t in
    match t with
    | TyUnknown
    | TyDynamic ->
        ()

    | TyBound _ ->
        Log.error "There should be no free variables here."

    | TyOpen point ->
        begin match get_fact env point with
        | Exclusive ->
            raise (EExclusive t)
        | Affine ->
            raise EAffine
        | Duplicable bitmap ->
            if Array.length bitmap != 0 then
              Log.error "Partial type applications are not allowed"
        | Fuzzy param_number ->
            (* Only the current type's parameters are marked as fuzzy. *)
            begin match phase with
            | Elaborating my_bitmap ->
                let my_arity = Array.length my_bitmap in
                Log.debug ~level:4 "↳ marking parameter %d" param_number;
                Log.check (param_number >= 0 && param_number < my_arity)
                  "Marking as duplicable a variable that's not in the right\
                  range! param_number = %d" param_number;
                my_bitmap.(param_number) <- true
            | Checking ->
                Log.error "No fuzzy variables should be present when checking."
            end
        end

    (*
     *
     * We could have a lower element called [any] in             aff
     * the fact lattice, and because these variables           /    \
     * are universal, they would have that fact.             dup   excl
     * However, we don't have it, so we can pick an            \    /
     * element as low as we want. We choose                     any
     * duplicable, because we know it's the optimal
     * choice given our limited set of facts.            fig 1: a better
     *                                                  lattice for facts
     * *)
    | TyForall ((binding, _), t') ->
        (* This variable is universal, so pick the best possible fact for it:
         * duplicable (see my notebook on Jan, 9th 2013) *)
        let env, t', var = bind_rigid_in_type env binding t' in
        let env = set_fact env var (Duplicable [||]) in
        follows_exclusive env t' t

    | TyExists (binding, t') ->
        (* Be conservative, bind as affine. *)
        let env, t', var = bind_rigid_in_type env binding t' in
        let env = set_fact env var Affine in
        follows_exclusive env t' t

    | TyApp (cons, args) ->
        begin match get_fact env !!cons with
        | Fuzzy _ ->
            Log.error "I messed up my index computations. Oops!";
        | Exclusive ->
            raise (EExclusive t)
        | Affine ->
            raise EAffine
        | Duplicable cons_bitmap ->
            (* For each argument of the type application... *)
            List.iteri (fun i ti ->
              (* The type at [level] may request its [i]-th parameter to be
               * duplicable. *)
              if cons_bitmap.(i) then begin
                (* The answer is yes: the [i]-th parameter for the type
                 * application is [ti] and it has to be duplicable for the
                 * type at [level] to be duplicable too. *)
                duplicables env ti
              end else begin
                (* The answer is no: there are no constraints on [ti]. *)
                ()
              end
            ) args
        end

    | TyTuple ts ->
        List.iter (duplicables env) ts

    | TyConcreteUnfolded (datacon, fields, _) as t ->
        let flag, _, _ = def_for_datacon env datacon in
        begin match flag with
        | SurfaceSyntax.Duplicable ->
            List.iter (function
              | FieldValue (_, typ)
              | FieldPermission typ ->
                  duplicables env typ
            ) fields
        | SurfaceSyntax.Exclusive ->
            raise (EExclusive t)
        end

    | TySingleton _ ->
        (* Singleton types are always duplicable. *)
        ()

    | TyArrow _ ->
        (* Arrows are always duplicable *)
        ()

    | TyAnchoredPermission (_, t') ->
        (* For x: τ to be duplicable, τ has to be duplicable as well *)
        duplicables env t'

    | TyEmpty ->
        ()

    | TyStar (p, q) ->
        (* For p ∗ q  to be duplicable, both p and q have to be duplicable. *)
        duplicables env p;
        duplicables env q

    | TyBar (t, p) ->
        duplicables env t;
        duplicables env p

    | TyAnd (constraints, t)
    | TyImply (constraints, t) ->
        (* XXX this is probably at best very much conservative, at worse
         * unsound. *)
        let ts = List.map snd constraints in
        List.iter (duplicables env) (t :: ts)
  in
  duplicables env t
;;

(* This performs one round of constraint propagation.
   - If the type is initially marked as Exclusive, it remains Exclusive.
   - If the type is marked as Duplicable, we recursively determine which ones of
   its type variables should be marked as duplicable for the whole type to be
   duplicable. *)
let one_round (env: env) (vars: var list): env =
  TypePrinter.(Log.debug ~level:4 "env:\n  %a" pdoc (print_binders, env));
  (* Folding on all the data types. *)
  List.fold_left (fun env var ->
    let names = get_names env var in
    let kind = get_kind env var in
    let fact = get_fact env var in
    let definition = get_definition env var in
    let tname = List.hd names in
    (* What knowledge do we have from the previous round? *)
    match definition with
    | None ->
        Log.error "Only data type definitions here"
    | Some (None, _) ->
        env
    | Some (Some (_flag, branches, clause), _) ->
        match fact with
        | Fuzzy _ ->
            Log.error "I messed up my index computations. Oops!";
        | Exclusive | Affine ->
            (* This fact cannot evolve anymore, pass [env] through. *)
            env
        | Duplicable bitmap ->
            Log.debug ~level:4 "Attacking %s%a%s %a" Bash.colors.Bash.red
              TypePrinter.pvar (env, get_name env var)
              Bash.colors.Bash.default
              TypePrinter.pvar (env, tname);
            (* [bitmap] is shared! *)
            let phase = Elaborating bitmap in
            let inner_env, _, branches, clause =
              bind_datacon_parameters env kind branches clause
            in
            Log.check (clause = None) "We allow adopts clauses for types marked \
              as exclusive, and these should start right away with the exclusive \
              flag, so we shouldn't be here.";
            TypePrinter.(Log.debug ~level:4 "inner_env:\n  %a" pdoc (print_binders, inner_env));
            try
              (* Iterating on the branches. *)
              List.iter (fun (_label, fields) ->
                (* Iterating on the fields. *)
                List.iter (function
                  | FieldValue (_, typ)
                  | FieldPermission typ ->
                      duplicables inner_env phase typ
                ) fields
              ) branches;
              env
            with EAffine | EExclusive _ ->
              (* Some exception was raised: the type, although initially
               * duplicable, contains a sub-part whose type is [Exclusive] or
               * [Affine], so the whole type need to be affine. *)
              set_fact env var Affine
  ) env vars
;;


let analyze_type (env: env) (t: typ): fact =
  try
    duplicables env Checking t;
    Duplicable [||]
  with
  | EExclusive t' when equal env t t' ->
      Exclusive
  | EExclusive _
  | EAffine ->
      Affine
;;

let is_duplicable env t =
  match analyze_type env t with
  | Duplicable [||] ->
      true
  | Duplicable _
  | Fuzzy _ ->
      Log.error "[is_duplicable] works only on types, not definitions, and must \
        be run after the fact elaboration phase is done"
  | Exclusive | Affine ->
      false
;;

let is_exclusive env t =
  analyze_type env t = Exclusive
;;

let analyze_data_types (env: env) (vars: var list): env =
  (* We could be even smarter and make the function return both a new env and a
   * boolean telling whether we udpated the maps or not, but that would require
   * threading some [was_modified] variable throughout all the code. Because
   * premature optimization is the root of all evil, let's leave it as is for
   * now. *)
  let rec run_to_fixvar env =
    Bash.(Log.debug ~level:2 "%sOne round of fact analysis...%s" colors.blue colors.default);
    (* We need to deep-copy, because the whole thing relies on the bitmap being
     * shared, mutable arrays. *)
    let copy_fact = function
      | Duplicable bitmap ->
          Duplicable (Array.copy bitmap)
      | _ as x ->
          x
    in
    let old_facts = List.map (fun var -> copy_fact (get_fact env var)) vars in
    (* We do a round of constraint propagation... *)
    let new_env = one_round env vars in
    let new_facts = List.map (get_fact new_env) vars in
    if new_facts <> old_facts then
      run_to_fixvar new_env
    else
      new_env
  in
  run_to_fixvar env
;;
