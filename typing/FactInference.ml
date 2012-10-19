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

open Types

(* ------------------------------------------------------------------------- *)

(* The core of the algorithm. *)

(* The [duplicables] function may throw either one of these two to indicate the
 * reason why the type it's currently analyzing is not duplicable. I'm not sure
 * the code always gives the most precise reason. *)
exception EAffine of typ
exception EExclusive of typ

(* The algorithm below can be used in two distinct phases. The first one
 * analyses a given data type definition, so the algorithm is allowed to request
 * that a parameter be duplicable for the whole type to be duplicable. The
 * second one tries to tell whether a given type is duplicable or not later on.
 * *)
type phase = Elaborating of bitmap | Checking

(* This function performs a reverse-analysis of a type. As it goes, it marks
 * those variables that needs to be duplicable by updating the bitmap contained
 * in [phase]. It may throw [EAffine] if it turns out the type it's
 * currently analyzing is affine. *)
let duplicables
    (env: env) 
    (phase: phase)
    (t: typ): unit =
  let rec duplicables (env: env) (t: typ): unit =
    match t with
    | TyUnknown
    | TyDynamic ->
        ()

    | TyVar _ ->
        Log.error "There should be no free variables here."

    | TyPoint point ->
        begin match structure env point with
        | Some t ->
            duplicables env t
        | None ->
            begin match get_fact env point with
            | Exclusive ->
                raise (EExclusive t)
            | Affine ->
                raise (EAffine t)
            | Duplicable bitmap ->
                if Array.length bitmap != 0 then
                  Log.error "Partial type applications are not allowed"
            | Fuzzy param_number ->
                (* Only the current type's parameters are marked as fuzzy. *)
                begin
                  match phase with
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
        end

    | TyForall ((binding, _), t)
    | TyExists (binding, t) ->
        let env, t = bind_var_in_type env binding t in
        duplicables env t

    | TyApp (cons, args) ->
        begin match get_fact env !!cons with
        | Fuzzy _ ->
            Log.error "I messed up my index computations. Oops!";
        | Exclusive ->
            raise (EExclusive t)
        | Affine ->
            raise (EAffine t)
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
      begin
        let flag, _, _ = def_for_datacon env datacon in
        begin
          match flag with
          | SurfaceSyntax.Duplicable ->
              List.iter (function
                | FieldValue (_, typ)
                | FieldPermission typ ->
                    duplicables env typ
              ) fields
          | SurfaceSyntax.Exclusive ->
              raise (EExclusive t)
        end
      end

    | TySingleton _ ->
        (* Singleton types are always duplicable. *)
        ()

    | TyArrow _ ->
        (* Arrows are always duplicable *)
        ()

    | TyAnchoredPermission (x, t') ->
        begin match x with
        | TyPoint p ->
            Log.check (is_term env p) "Malformed term %a"
              TypePrinter.ptype (env, t)
        | _ ->
            Log.error "Malformed type %a" TypePrinter.ptype (env, t)
        end;
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

    | TyConstraints (constraints, t) ->
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
let one_round (env: env) (points: point list): env =
  TypePrinter.(Log.debug ~level:4 "env:\n  %a" pdoc (print_binders, env));
  (* Folding on all the data types. *)
  List.fold_left (fun env point ->
    let names = get_names env point in
    let kind = get_kind env point in
    let fact = get_fact env point in
    let definition = get_definition env point in
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
              TypePrinter.pvar (get_name env point)
              Bash.colors.Bash.default
              TypePrinter.pvar tname;
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
            with EAffine _t | EExclusive _t ->
              (* Some exception was raised: the type, although initially
               * duplicable, contains a sub-part whose type is [Exclusive] or
               * [Affine], so the whole type need to be affine. *)
              replace_type env point (fun entry -> { entry with fact = Affine })
  ) env points
;;


(* If this function is correct (and I'm not even sure of that), it only is for
 * types that have been expanded (it would return Exclusive for
 * [(xpair int int, int)], for instance, instead of affine. *)
let analyze_type (env: env) (t: typ): fact =
  try
    duplicables env Checking t;
    Duplicable [||]
  with
  | EExclusive t' when t == t' ->
      Exclusive
  | EExclusive _
  | EAffine _ ->
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
  | _ ->
      false
;;

let is_exclusive env t =
  analyze_type env t = Exclusive
;;

let analyze_data_types (env: env) (points: point list): env =
  (* We could be even smarter and make the function return both a new env and a
   * boolean telling whether we udpated the maps or not, but that would require
   * threading some [was_modified] variable throughout all the code. Because
   * premature optimization is the root of all evil, let's leave it as is for
   * now. *)
  let rec run_to_fixpoint env =
    Bash.(Log.debug ~level:2 "%sOne round of fact analysis...%s" colors.blue colors.default);
    let copy_fact = function
      | Duplicable bitmap ->
          Duplicable (Array.copy bitmap)
      | _ as x ->
          x
    in
    (* This works because [map_types] guarantees an unspecified, but fixed,
     * order, and because [replace_type] doesn't change that order. *)
    let old_facts = List.map (fun point -> copy_fact (get_fact env point)) points in
    let new_env = one_round env points in
    let new_facts = List.map (fun point -> copy_fact (get_fact new_env point)) points in
    (* Hml_List.iter2i (fun level old_fact new_fact ->
      let index = ByIndex.cardinal env.bindings - level - 1 in
      Log.debug ~level:3
        "name %s\t index %d bitmap %a\t | bitmap %a"
        (name_for_type env index)
        index
        TypePrinter.pdoc (TypePrinter.do_print_fact, old_fact)
        TypePrinter.pdoc (TypePrinter.do_print_fact, new_fact);
    ) old_facts new_facts; *)
    if new_facts <> old_facts then
      run_to_fixpoint new_env
    else
      new_env
  in
  run_to_fixpoint env
;;
