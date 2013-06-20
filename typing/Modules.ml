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
module S = SurfaceSyntax
module E = Expressions

(* For internal use only (yet). *)
let collect_dependencies (items: S.toplevel_item list): Module.name list =
  let open SurfaceSyntax in

  let rec collect_items items =
    MzList.flatten_map collect_item items

  and collect_item = function
    | ValueDeclaration (_, ty) ->
        collect_type ty
    | DataTypeGroup (_, _, defs) ->
        MzList.flatten_map (function def ->
         match def.rhs with
          | Abstract _ ->
              []
          | Abbrev t ->
              collect_type t
          | Concrete (_flag, rhs, adopts) ->
              Option.map_none [] (Option.map collect_type adopts)
              @ MzList.flatten_map collect_data_type_def_branch rhs
        ) defs
    | ValueDefinitions (_, _, patexprs) ->
        collect_patexprs patexprs
    | OpenDirective m ->
        [m]

  and collect_patexprs patexprs =
    let pats, exprs = List.split patexprs in
    MzList.flatten_map collect_pattern pats
    @ MzList.flatten_map collect_expr exprs

  and collect_pattern = function
    | PVar _ ->
        []
    | PLocated (p1, _) ->
        collect_pattern p1
    | PConstraint (p1, t1) ->
        collect_pattern p1 @ collect_type t1
    | PTuple ps ->
        MzList.flatten_map collect_pattern ps
    | PConstruct (dref, namepats) ->
        let _, ps = List.split namepats in
        MzList.flatten_map collect_pattern ps @
        collect_maybe_qualified dref.datacon_unresolved
    | PAs (p1, _) ->
        collect_pattern p1
    | PAny ->
        []

  and collect_expr = function
    | EConstraint (expr, t) ->
        collect_expr expr @ collect_type t
    | EVar x ->
        collect_maybe_qualified x
    | EBuiltin _
    | EInt _
    | EFail ->
        []
    | EMatch (_, expr, patexprs)
    | ELet (_, patexprs, expr) ->
        collect_patexprs patexprs @ collect_expr expr
    | ELetFlex (_, t, e) ->
        collect_type t @ collect_expr e
    | EFun (_, t1, t2, expr) ->
        collect_type t1 @ collect_type t2 @ collect_expr expr
    | EAssign (e1, _, e2)
    | EApply (e1, e2)
    | EGive (e1, e2)
    | ETake (e1, e2)
    | EOwns (e1, e2)
    | ESequence (e1, e2) ->
        collect_expr e1 @ collect_expr e2
    | ELocated (expr, _)
    | EAccess (expr, _)
    | EExplained expr ->
        collect_expr expr
    | EAssignTag (expr, dref, _) ->
        collect_expr expr @
        collect_maybe_qualified dref.datacon_unresolved
    | EAssert t ->
        collect_type t
    | ETApply (expr, ts) ->
        collect_expr expr @
        MzList.flatten_map (function
         | Ordered x
         | Named (_, x) ->
          collect_type x
        ) ts
    | ETuple exprs ->
        MzList.flatten_map collect_expr exprs
    | EConstruct (dref, nameexprs) ->
        let _, exprs = List.split nameexprs in
        MzList.flatten_map collect_expr exprs @
        collect_maybe_qualified dref.datacon_unresolved
    | EIfThenElse (_, e1, e2, e3) ->
        collect_expr e1 @ collect_expr e2 @ collect_expr e3
    | EWhile (t, e1, e2) ->
        collect_type t @ collect_expr e1 @ collect_expr e2
    | EFor (t, _, e1, _, e2, e) ->
        collect_type t @ collect_expr e1 @ collect_expr e2 @ collect_expr e

  and collect_type = function
    | TyVar v ->
        collect_maybe_qualified v
    | TyUnknown
    | TyDynamic
    | TyEmpty
        -> []
    | TySingleton t1
    | TyNameIntro (_, t1)
    | TyConsumes t1
    | TyLocated (t1, _)
    | TyForall (_, t1)
    | TyExists (_, t1) ->
        collect_type t1
    | TyArrow (t1, t2)
    | TyAnchoredPermission (t1, t2)
    | TyBar (t1, t2)
    | TyStar (t1, t2)
    | TyAnd ((_, t1), t2)
    | TyImply ((_, t1), t2) ->
        collect_type t1 @ collect_type t2
    | TyTuple ts ->
        MzList.flatten_map collect_type ts
    | TyApp (t, ts) ->
        MzList.flatten_map collect_type (t :: ts)
    | TyConcrete (branch, clause) ->
        collect_data_type_def_branch branch @
        collect_maybe_qualified (fst branch).datacon_unresolved @
       MzList.flatten_map collect_type (Option.to_list clause)

  and collect_data_type_def_branch: 'a. 'a * data_field_def list -> Module.name list =
  fun (_, fields)  ->
    let ts = List.map (function
      | FieldValue (_, t) ->
          t
      | FieldPermission t ->
          t
    ) fields in
    MzList.flatten_map collect_type ts

  and collect_maybe_qualified: 'a. 'a maybe_qualified -> Module.name list =
  function
    | Unqualified _ -> []
    | Qualified (m, _) -> [m]

  in

  collect_items items
;;

(* Called by [Driver], returns all the dependencies (transitive) of [items],
 * sorted by topological order. *)
let all_dependencies (mname: Module.name) (find: Module.name -> S.toplevel_item list): Module.name list =
  (* Not in the hash-table = not visited, Gray = visiting, Black = visited *)
  let module T = struct type t = White | Gray | Black end in
  let open T in
  let h = Hashtbl.create 13 in
  let l = ref [] in
  let rec collect name = 
    let color =
      try Hashtbl.find h name
      with Not_found -> White
    in
    match color with
    | Black ->
        ()
    | Gray ->
        let open TypeErrors in
        raise_error TypeCore.empty_env (CyclicDependency name)
    | White ->
        Hashtbl.add h name Gray;
        let deps = collect_dependencies (find name) in
        List.iter collect deps;
        l := name :: !l;
        Hashtbl.add h name Black
  in
  collect mname;
  (* The module does not depend on itself. *)
  let l = List.tl !l in
  let l = List.rev l in
  let names = String.concat ", " (List.map Module.print l) in
  Log.debug "Found dependencies for %a (left-to-right) = %s" Module.p mname names;
  l
;;
