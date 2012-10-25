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

(* I'm defining module abbreviations because we're juggling with all these
 * modules at the same time, and the names conflict (e.g. env, toplevel_item,
 * etc.). *)
module T = Types
module S = SurfaceSyntax
module E = Expressions

(* Used by [Driver], to import the points from a desugared interface into
 * another one, prefixed by the module they belong to, namely [mname]. *)
let import_interface (env: T.env) (items: E.interface): T.env =
  let open Types in
  let open Expressions in
  (* We demand that [env] have the right module name. *)
  let rec import_items env = function
    | PermDeclaration (name, typ) :: items ->
        (* XXX the location information is probably wildly inaccurate *)
        let binding = User (env.module_name, name), KTerm, env.location in
        let env, p = bind_var env binding in
        let typ, _ = TypeOps.cleanup_function_type env typ None in
        let env = Permissions.add env p typ in
        let items = tsubst_toplevel_items (TyPoint p) 0 items in
        let items = esubst_toplevel_items (EPoint p) 0 items in
        import_items env items

    | DataTypeGroup group :: items ->
        let env, items = DataTypeGroup.bind_data_type_group env group items in
        import_items env items

    | ValueDeclarations _ :: _ ->
        assert false

    | [] ->
        env
  in

  import_items env items
;;

(* For internal use only (yet). *)
let collect_dependencies (items: S.toplevel_item list): Module.name list =
  let open SurfaceSyntax in

  (* Just so we're clear: among these functions, only collect_item actually does
   * something in the [OpenDirective] case. But this will all change we have
   * prefixed names and prefixed constructors... *)

  let rec collect_items items =
    Hml_List.map_flatten collect_item items

  and collect_item = function
    | PermDeclaration t ->
        collect_type t
    | DataTypeGroup (_, defs) ->
        Hml_List.map_flatten (function
          | Abstract _ ->
              []
          | Concrete (_flag, _lhs, rhs, adopts) ->
              Option.map_none [] (Option.map collect_type adopts)
              @ Hml_List.map_flatten collect_data_type_def_branch rhs
        ) defs
    | ValueDeclarations decls ->
        Hml_List.map_flatten collect_decl decls
    | OpenDirective m ->
        [m]

  and collect_decl = function
    | DLocated (d, _, _) ->
        collect_decl d
    | DMultiple (_, patexprs) ->
        collect_patexprs patexprs

  and collect_patexprs patexprs =
    let pats, exprs = List.split patexprs in
    Hml_List.map_flatten collect_pattern pats
    @ Hml_List.map_flatten collect_expr exprs

  and collect_pattern = function
    | PVar _ ->
        []
    | PLocated (p1, _, _) ->
        collect_pattern p1
    | PConstraint (p1, t1) ->
        collect_pattern p1 @ collect_type t1
    | PTuple ps ->
        Hml_List.map_flatten collect_pattern ps
    | PConstruct (_, namepats) ->
        let _, ps = List.split namepats in
        Hml_List.map_flatten collect_pattern ps
    | PAs (p1, p2) ->
        collect_pattern p1 @ collect_pattern p2

  and collect_expr = function
    | EQualified (m, _) ->
        [m]
    | EConstraint (expr, t) ->
        collect_expr expr @ collect_type t
    | EVar _
    | EInt _
    | EFail ->
        []
    | EMatch (_, expr, patexprs)
    | ELet (_, patexprs, expr) ->
        collect_patexprs patexprs @ collect_expr expr
    | EFun (_, t1, t2, expr) ->
        collect_type t1 @ collect_type t2 @ collect_expr expr
    | EAssign (e1, _, e2)
    | EApply (e1, e2)
    | EGive (e1, e2)
    | ETake (e1, e2)
    | ESequence (e1, e2) ->
        collect_expr e1 @ collect_expr e2
    | ELocated (expr, _, _)
    | EAssignTag (expr, _)
    | EAccess (expr, _)
    | EExplained expr ->
        collect_expr expr
    | EAssert t ->
        collect_type t
    | ETApply (expr, ts) ->
        collect_expr expr @ Hml_List.map_flatten collect_type ts
    | ETuple exprs ->
        Hml_List.map_flatten collect_expr exprs
    | EConstruct (_, nameexprs) ->
        let _, exprs = List.split nameexprs in
        Hml_List.map_flatten collect_expr exprs
    | EIfThenElse (_, e1, e2, e3) ->
        collect_expr e1 @ collect_expr e2 @ collect_expr e3

  and collect_type = function
    | TyQualified (m, _) ->
        [m]
    | TyUnknown
    | TyDynamic
    | TyEmpty
    | TyVar _ ->
        []
    | TySingleton t1
    | TyNameIntro (_, t1)
    | TyConsumes t1
    | TyLocated (t1, _, _)
    | TyForall (_, t1) ->
        collect_type t1
    | TyApp (t1, t2)
    | TyArrow (t1, t2)
    | TyAnchoredPermission (t1, t2)
    | TyBar (t1, t2)
    | TyStar (t1, t2) ->
        collect_type t1 @ collect_type t2
    | TyTuple ts ->
        Hml_List.map_flatten collect_type ts
    | TyConstraints (dcs, t) ->
        let _, ts = List.split dcs in
        collect_type t @ Hml_List.map_flatten collect_type ts
    | TyConcreteUnfolded branch ->
        collect_data_type_def_branch branch

  and collect_data_type_def_branch (_, fields) =
    let ts = List.map (function
      | FieldValue (_, t) ->
          t
      | FieldPermission t ->
          t
    ) fields in
    Hml_List.map_flatten collect_type ts

  in

  collect_items items
;;

(* Called by [Driver], returns all the dependencies (transitive) of [items],
 * sorted by topological order. *)
let all_dependencies (mname: Module.name) (find: Module.name -> S.toplevel_item list): Module.name list =
  let h = Hashtbl.create 13 in
  let l = ref [] in
  let rec collect name = 
    if Hashtbl.mem h name then begin
      ()
    end else begin
      Hashtbl.add h name ();
      let deps = collect_dependencies (find name) in
      List.iter collect deps;
      l := name :: !l
    end
  in
  collect mname;
  let l = List.tl !l in
  let l = List.rev l in
  (* The module does not depend on itself. *)
  let names = String.concat ", " (List.map Module.print l) in
  Log.debug "Found dependencies for %a (left-to-right) = %s" Module.p mname names;
  l
;;
