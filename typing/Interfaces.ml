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

(** This module helps dealing with interfaces. *)

module S = SurfaceSyntax
module E = Expressions
module T = TypeCore
module TS = TransSurface

(* ---------------------------------------------------------------------------- *)

(* [build_interface env mname] finds the right interface file for [mname], and
 * lexes it, parses it, and returns a desugared version of it, ready for
 * importing into some environment. *)
let build_interface (env: TypeCore.env) (mname: Module.name) (iface: S.interface): T.env * E.interface =
  let env = TypeCore.set_module_name env mname in
  KindCheck.check_interface env iface;
  env, TransSurface.translate_interface env iface
;;

(* Used by [Driver], to import the points from a desugared interface into
 * another one, prefixed by the module they belong to, namely [mname]. *)
let import_interface (env: T.env) (mname: Module.name) (iface: S.interface): T.env =
  Log.debug "Massive import, %a" Module.p mname;
  let env, iface = build_interface env mname iface in

  let open TypeCore in
  let open Expressions in
  (* We demand that [env] have the right module name. *)
  let rec import_items env = function
    | PermDeclaration (name, typ) :: items ->
        (* XXX the location information is probably wildly inaccurate *)
        let binding = User (module_name env, name), KTerm, location env in
        let env, p = bind_rigid env binding in
        (* [add] takes care of simplifying any function type. *)
        let env = Permissions.add env p typ in
        let items = tsubst_toplevel_items (TyOpen p) 0 items in
        let items = esubst_toplevel_items (EOpen p) 0 items in
        import_items env items

    | DataTypeGroup group :: items ->
        let env, items, _ = DataTypeGroup.bind_data_type_group env group items in
        import_items env items

    | ValueDeclarations _ :: _ ->
        assert false

    | [] ->
        env
  in

  import_items env iface
;;

(* Check that [env] respect the [signature] which is that of module [mname]. We
 * will want to check that [env] respects its own signature, but also that of
 * the modules it exports, i.e. that it leaves them intact.
 *
 * Why does this function return an environment? Well, when we're type-checking
 * a module against its own signature, we need to return the environment
 * afterwards, because we may have consumed permissions from other modules, and
 * [Driver] will want to check that for us (by eventually calling us again with
 * another [mname]). *)
let check
  (env: T.env)
  (signature: S.toplevel_item list)
  (exports: (Variable.name * T.kind * T.var) list)
: T.env =
  (* Find one specific name among these names. *)
  let point_by_name name =
    match MzList.find_opt (fun (name', _, p') ->
      if Variable.equal name name' then
        Some p'
      else
        None
    ) exports with
    | Some p ->
        p
    | None ->
        List.iter (fun (name, _, _) ->
          Log.debug "%a" Variable.p name
        ) exports;
        let open TypeErrors in
        raise_error env (MissingFieldInSignature name)
  in

  (* As [check] processes one toplevel declaration after another, it first add
   * the name into the translation environment (i.e. after processing [val foo @ τ],
   * [foo] is known to point to a point in [env] in [tsenv]). Second, in
   * order to check [val foo @ τ], it removes [τ] from the list of available
   * permissions for [foo] in [env], which depletes as we go. *)
  let rec check (env: T.env) (tsenv: KindCheck.env) (toplevel_items: S.toplevel_item list) =
    match toplevel_items with
    | S.OpenDirective mname :: toplevel_items ->
        let tsenv = KindCheck.open_module_in mname tsenv in
        check env tsenv toplevel_items

    | S.PermDeclaration (x, t) :: toplevel_items ->
        (* val x: t *)
        Log.debug ~level:3 "*** Checking sig item %a" Variable.p x;

        (* Make sure [t] has kind ∗ *)
        KindCheck.check tsenv t S.KType;

        (* Now translate type [t] into the internal syntax; [x] is not bound in
         * [t]. *)
        let t = TransSurface.translate_type tsenv t in

        (* Now check that the point in the implementation's environment actually
         * has the same type as the one in the interface. *)
        let point = point_by_name x in
        let env =
          match Permissions.sub env point t with
          | Some env ->
              env
          | None ->
              let open TypeErrors in
              raise_error env (NoSuchTypeInSignature (point, t))
        in

        (* Alright, [x] is now bound, and when it appears afterwards, it will
         * refer to the original [x] from [env]. *)
        let tsenv = KindCheck.bind_external tsenv (x, S.KTerm, point) in

        (* Check the remainder of the toplevel_items. *)
        check env tsenv toplevel_items

    | S.DataTypeGroup group :: toplevel_items ->
        (* We first collect the names of all the data types. *)
        let group = snd group in
        let bindings = KindCheck.bindings_data_type_group group in

        (* And associate them to the corresponding definitions in [env]. *)
        let bindings = List.map (fun (name, k) ->
          let point = point_by_name name in
          name, k, point
        ) bindings in

        (* Translate the data types definitions so that they refer to the
         * "original" points from [env]. *)
        let tsenv = List.fold_left KindCheck.bind_external tsenv bindings in
        (* Don't forget to bind the data constructors. *)
        let tsenv = TS.bind_datacons tsenv group in
        (* Do the translation *)
        let translated_definitions =
          List.map (TS.translate_data_type_def tsenv) group
        in

        (* Check that the translated definitions from the interface in the known
         * definitions from the implementations are consistent. *)
        List.iter2 (fun (name, k, point) (name', _loc, def, fact, kind) ->
          (* Variables marked with ' belong to the implementation. *)
          let open TypeErrors in

          Log.check (Variable.equal name name') "Names not in order?!";
          Log.check (k = kind) "Inconsistency?!";
          let error_out reason =
            raise_error env (DataTypeMismatchInSignature (name, reason))
          in

          (* Check kinds. *)
          let k' = T.get_kind env point in
          if k <> k' then
            error_out "kinds";

          (* Check facts. We check that the fact in the implementation is more
           * precise than the fact in the signature. *)
          let fact' = T.get_fact env point in

          (* Definitions. *)
          let def' = Option.extract (T.get_definition env point) in
          let def, variance = def in
          let def', variance' = def' in

          if not (List.for_all2 Variance.leq variance' variance) then
            error_out "variance";

          match def, def' with
          | None, None ->
              (* When re-matching a module against the interfaces it opened,
               * we'll encounter the case where in [env] the type is defined as
               * abstract, and in the signature it is still abstract.
               *
               * [TransSurface] authorizes declaring a type as abstract
               * in an implementation: we just re-check the fact, since the
               * kinds have been checked earlier already. *)
              if not (Types.fact_leq fact' fact) then
                error_out "facts";

          | None, Some _ ->
              (* Type made abstract. We just check that the facts are
               * consistent. The fact information in [fact'] (the
               * implementation) is correct, since [Driver] took care of running
               * [DataTypeGroup.bind_data_type_group]. The fact from the
               * interface, i.e. [fact], is correct because the fact for an
               * abstract is purely syntactical and does not depend on having
               * run [FactInferenceBis.analyze_types] properly. *)
              if not (Types.fact_leq fact' fact) then
                error_out "facts";

          | Some _, None ->
              error_out "type abstract in implem but not in sig";

          | Some (flag, branches, clause), Some (flag', branches', clause') ->
              (* We're not checking facts: if the flag and the branches are
               * equal, then it results that the facts are equal. Moreover, we
               * haven't run [FactInferenceBis.analyze_types] on the *signature* so
               * the information in [fact] is just meaningless. *)

              if flag <> flag' then
                error_out "flags";

              begin match clause, clause' with
              | Some clause, Some clause' ->
                  if not (T.equal env clause clause') then
                    error_out "clauses";
              | None, None ->
                  ()
              | Some _, None
              | None, Some _ ->
                  error_out "clause in only one of sig, implem";
              end;

              List.iter2 (fun (datacon, fields) (datacon', fields') ->
                if not (Datacon.equal datacon datacon') then
                  error_out "datacons";
                List.iter2 (fun field field' ->
                  match field, field' with
                  | T.FieldValue (fname, t), T.FieldValue (fname', t') ->
                      if not (Variable.equal fname fname') then
                        error_out "field names";
                      if not (T.equal env t t') then
                        error_out "field defs";
                  | T.FieldPermission t, T.FieldPermission t' ->
                      if not (T.equal env t t') then
                        error_out "permission field";
                  | _ ->
                      error_out "field nature";
                ) fields fields';
              ) branches branches';

        ) bindings translated_definitions;

        (* Check the remainder of the toplevel_items. *)
        check env tsenv toplevel_items


    | S.ValueDeclarations _ :: _ ->
        assert false

    | [] ->
        env
  in

  check env (KindCheck.empty env) signature
;;
