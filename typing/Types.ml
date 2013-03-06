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

(** This module provides various helpers that help dealing with types. It also
 * re-exports most type-related functions. *)

open TypeCore
open DeBruijn

(* ---------------------------------------------------------------------------- *)

(* Fact-related functions. *)

let fact_leq f1 f2 =
  match f1, f2 with
  | _, Affine ->
      true
  | _ when f1 = f2 ->
      true
  | Duplicable b1, Duplicable b2 ->
      let (<=) b1 b2 = match b1, b2 with
        | true, false ->
            false
        | _ ->
            true
      in
      let v = ref true in
      v := !v && Array.length b1 = Array.length b2;
      for i = 0 to Array.length b1 - 1 do
        (* Covariant! *)
        v := !v && b2.(i) <= b1.(i)
      done;
      !v
  | _ ->
      false
;;

let fact_of_flag = function
  | SurfaceSyntax.Exclusive ->
      Exclusive
  | SurfaceSyntax.Duplicable ->
      Duplicable [||]
;;


(* ---------------------------------------------------------------------------- *)

(* Various helpers for creating and destructuring [typ]s easily. *)

(* Saves us the trouble of matching all the time. *)
let ( |>  ) x f   = f x;;
let ( !*  )       = Lazy.force;;
let ( >>= )       = Option.bind;;
let ( ||| ) o1 o2 = if Option.is_some o1 then o1 else o2 ;;
let ( ^=> ) x y   = x && y || not x;;

let ( !!  )       = function
  | TyOpen x -> x
  | _ as t -> Log.error "Not a TyOpen %a" !internal_ptype (empty_env, t);;

let ( !!= )       = function
  | TySingleton (TyOpen x) ->
      x
  | _ ->
      assert false
;;

let fst3 (x, _, _) = x;;
let snd3 (_, x, _) = x;;
let thd3 (_, _, x) = x;;

let is_user = function User _ -> true | Auto _ -> false;;

let ty_equals x =
  TySingleton (TyOpen x)
;;

let ty_unit =
  TyTuple []
;;

let ty_tuple ts =
  TyTuple ts
;;

let ty_bottom =
  TyForall (
    (
      (Auto (Variable.register "⊥"), KType, (Lexing.dummy_pos, Lexing.dummy_pos)),
      CannotInstantiate
    ),
    TyBound 0
  )

(* This is right-associative, so you can write [list int @-> int @-> tuple []] *)
let (@->) x y =
  TyArrow (x, y)
;;

let ty_bar t p =
  if p = TyEmpty then
    t
  else
    TyBar (t, p)
;;

let ty_app t args =
  if List.length args > 0 then
    TyApp (t, args)
  else
    t
;;

let flatten_kind = SurfaceSyntax.flatten_kind;;

let rec flatten_star env t =
  let t = modulo_flex env t in
  match t with
  | TyStar (p, q) ->
      flatten_star env p @ flatten_star env q
  | TyEmpty ->
      []
  | TyOpen _
  | TyBound _
  | TyAnchoredPermission _
  | TyApp _ ->
      [t]
  | _ ->
      Log.error "[flatten_star] only works for types with kind perm"
;;

let fold_star perms =
  if List.length perms > 0 then
    MzList.reduce (fun acc x -> TyStar (acc, x)) perms
  else
    TyEmpty
;;

let strip_forall t =
  let rec strip acc = function
  | TyForall (b, t) ->
      strip (b :: acc) t
  | _ as t ->
      List.rev acc, t
  in
  strip [] t
;;

let fold_forall bindings t =
  List.fold_right (fun binding t ->
    TyForall (binding, t)
  ) bindings t
;;

let fold_exists bindings t =
  List.fold_right (fun binding t ->
    TyExists (binding, t)
  ) bindings t
;;

let fresh_auto_var prefix = Auto (Utils.fresh_var prefix);;



(* -------------------------------------------------------------------------- *)

(* Various functions related to binding and finding. *)

(* When crossing a binder, say, [a : type], use this function to properly add
 * [a] in scope. *)
let bind_in_type
    (bind: env -> type_binding -> env * var)
    (env: env)
    (binding: type_binding)
    (typ: typ): env * typ * var
  =
  let env, var = bind env binding in
  let typ = tsubst (TyOpen var) 0 typ in
  env, typ, var
;;

let bind_rigid_in_type = bind_in_type bind_rigid;;
let bind_flexible_in_type = bind_in_type bind_flexible;;


(* Functions for traversing the binders list. Bindings are traversed in an
 * unspecified, but fixed, order. The [replace_*] functions preserve the order.
 *
 * Indeed, it turns out that the implementation of [PersistentUnionFind] is such
 * that:
 * - when updating a descriptor, the entry in the persistent store is
 * udpated in the same location,
 * - [map_types] is implemented using [PersistentUnionFind.fold] which is in
 * turn implemented using [PersistentRef.fold], itself a proxy for
 * [Patricia.Little.fold]. The comment in [patricia.ml] tells us that fold
 * runs over the keys in an unspecified, but fixed, order.
*)

(* let map_types env f =
  MzList.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | (head, BType b) -> Some (f head b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map_terms env f =
  MzList.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | (head, BTerm b) -> Some (f head b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map env f =
  List.rev
    (PersistentUnionFind.fold
      (fun acc _k ({ names; _ }, binding) -> f names binding :: acc)
      [] env.state)
;;

let fold_terms env f acc =
  PersistentUnionFind.fold (fun acc k (head, binding) ->
    match binding with BTerm b -> f acc k head b | _ -> acc)
  acc env.state
;;

let fold_types env f acc =
  PersistentUnionFind.fold (fun acc k (head, binding) ->
    match binding with BType b -> f acc k head b | _ -> acc)
  acc env.state
;;

let replace env point f =
  { env with state = PersistentUnionFind.update f point env.state }
;;

let replace_term env point f =
  { env with state =
      PersistentUnionFind.update (function
        | names, BTerm b ->
            names, BTerm (f b)
        | _ ->
            Log.error "Not a term"
      ) point env.state
  }
;;

let replace_type env point f =
  { env with state =
      PersistentUnionFind.update (function
        | names, BType b ->
            names, BType (f b)
        | _ ->
            Log.error "Not a type"
      ) point env.state
  }
;; *)



(* ---------------------------------------------------------------------------- *)

(* A hodge-podge of getters. *)

let get_name env p =
  let names = get_names env p in
  try
    List.find (function User _ -> true | Auto _ -> false) names
  with Not_found ->
    List.hd names
;;

let get_location env p =
  List.hd (get_locations env p)
;;

let get_adopts_clause env point: adopts_clause =
  match get_definition env point with
  | Some (Some (_, _, clause), _) ->
      clause
  | _ ->
      (* An abstract exclusive type has no adopts clause (as of now). *)
      None
;;

let get_branches env point: data_type_def_branch list =
  match get_definition env point with
  | Some (Some (_, branches, _), _) ->
      branches
  | _ ->
      Log.error "This is not a concrete data type."
;;

let get_arity (env: env) (var: var): int =
  get_arity_for_kind (get_kind env var)
;;

let rec get_kind_for_type env t =
  match modulo_flex env t with
  | TyBound _ ->
      Log.error "No free variables"
  | TyOpen p ->
      get_kind env p

  | TyForall ((binding, _), t)
  | TyExists (binding, t) ->
      let env, t, _ = bind_rigid_in_type env binding t in
      get_kind_for_type env t

  | TyApp (p, _) ->
      let return_kind, _ = flatten_kind (get_kind env !!p) in
      return_kind

  | TyUnknown
  | TyDynamic
  | TySingleton _
  | TyArrow _
  | TyBar _
  | TyTuple _
  | TyConcreteUnfolded _ ->
      KType

  | TyAnchoredPermission _
  | TyEmpty
  | TyStar _ ->
      KPerm

  | TyImply (_, t)
  | TyAnd (_, t) ->
      get_kind_for_type env t
;;


let get_variance (env: env) (var: var): variance list =
  match get_definition env var with
  | Some (_, v) ->
      v
  | None ->
      assert false
;;

let def_for_datacon (env: env) (datacon: resolved_datacon): SurfaceSyntax.data_type_flag * data_type_def * adopts_clause=
  match datacon with
  | TyOpen point, _ ->
      let def, _ = Option.extract (get_definition env point) in
      Option.extract def
  | t, _ ->
      Log.error "Datacon not properly resolved: %a" !internal_ptype (env, t)
;;

let variance env var i =
  let definition = get_definition env var in
  let variance = snd (Option.extract definition) in
  List.nth variance i
;;


(* ---------------------------------------------------------------------------- *)

(* Instantiating. *)

let instantiate_adopts_clause clause args =
  let clause = Option.map_none ty_bottom clause in
  let args = List.rev args in
  MzList.fold_lefti (fun i clause arg -> tsubst arg i clause) clause args
;;

let instantiate_branch branch args =
  let args = List.rev args in
  let branch = MzList.fold_lefti (fun i branch arg ->
    tsubst_data_type_def_branch arg i branch) branch args
  in
  branch
;;

let find_and_instantiate_branch
    (env: env)
    (var: var)
    (datacon: Datacon.name)
    (args: typ list) =
  let branch =
    List.find
      (fun (datacon', _) -> Datacon.equal datacon datacon')
      (get_branches env var)
  in
  let dc, fields = instantiate_branch branch args in
  let clause = instantiate_adopts_clause (get_adopts_clause env var) args in
  (TyOpen var, dc), fields, clause
;;

(* Misc. *)

(** This function is actually fairly ugly. This is a temporary solution so that
    [TypeChecker] as well as the test files can refer to type constructors
    defined in the file (e.g. int), for type-checking arithmetic expressions, for
    instance... *)
let find_type_by_name env ?mname name =
  let name = Variable.register name in
  let mname = Option.map Module.register mname in
  TyOpen (point_by_name env ?mname name)
;;

let is_tyapp = function
  | TyOpen p ->
      Some (p, [])
  | TyApp (p, args) ->
      Some ((match p with
        | TyOpen p ->
            p
        | _ ->
            assert false), args)
  | _ ->
      None
;;

let is_term env v = (get_kind env v = KTerm);;
let is_perm env v = (get_kind env v = KPerm);;
let is_type env v = (fst (flatten_kind (get_kind env v)) = KType);;

let make_datacon_letters env kind flexible f =
  let _return_kind, arg_kinds = flatten_kind kind in
  (* Turn the list of parameters into letters *)
  let letters: string list = MzPprint.name_gen (List.length arg_kinds) in
  let env, points = MzList.fold_left2i (fun i (env, points) kind letter ->
    let env, point =
      let letter = Auto (Variable.register letter) in
      let env, var =
        if flexible then
          bind_flexible env (letter, kind, location env)
        else
          bind_rigid env (letter, kind, location env)
      in
      set_fact env var (f i), var
    in
    env, point :: points) (env, []) arg_kinds letters
  in
  let points = List.rev points in
  env, points
;;

let bind_datacon_parameters (env: env) (kind: kind) (branches: data_type_def_branch list) (clause: adopts_clause):
    env * var list * data_type_def_branch list * adopts_clause =
  let env, points = make_datacon_letters env kind false (fun i -> Fuzzy i) in
  let arity = get_arity_for_kind kind in
  let branches, clause = MzList.fold_lefti (fun i (branches, clause) point ->
    let index = arity - i - 1 in
    let branches = List.map (tsubst_data_type_def_branch (TyOpen point) index) branches in
    let clause = Option.map (tsubst (TyOpen point) index) clause in
    branches, clause
  ) (branches, clause) points in
  env, points, branches, clause
;;

let expand_if_one_branch (env: env) (t: typ) =
  match is_tyapp t with
  | Some (cons, args) ->
      begin match get_definition env cons with
      | Some (Some (_, [branch], clause), _) ->
          let dc, fields = instantiate_branch branch args in
          let clause = instantiate_adopts_clause clause args in
          TyConcreteUnfolded ((TyOpen cons, dc), fields, clause)
      | _ ->
        t
      end
  | None ->
      t
;;


(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  open MzPprint

  (* If [f arg] returns a [document], then write [Log.debug "%a" pdoc (f, arg)] *)
  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    ToBuffer.pretty 1.0 Bash.twidth buf (f env)
  ;;

  (* --------------------------------------------------------------------------- *)

  let print_var env = function
    | User (m, var) when Module.equal (module_name env) m ->
        utf8string (Variable.print var)
    | User (m, var) ->
        utf8string (Module.print m) ^^ ccolon ^^ utf8string (Variable.print var)
    | Auto var ->
        colors.yellow ^^ utf8string (Variable.print var) ^^ colors.default
  ;;

  let pvar buf (env, var) =
    pdoc buf (print_var env, var)
  ;;

  let print_datacon datacon =
    utf8string (Datacon.print datacon)
  ;;

  let print_field_name field =
    utf8string (Field.print field)
  ;;

  let print_field field =
    print_field_name (field.SurfaceSyntax.field_name)
  ;;

  let rec print_kind =
    let open SurfaceSyntax in
    function
    | KTerm ->
        string "term"
    | KPerm ->
        string "perm"
    | KType ->
        string "type"
    | KArrow (k1, k2) ->
        print_kind k1 ^^ space ^^ arrow ^^ space ^^ print_kind k2
  ;;

  (* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
  let p_kind buf kind =
    pdoc buf (print_kind, kind)
  ;;

  let print_names env names =
    if List.length names > 0 then
      let names = List.map (print_var env) names in
      let names = List.map (fun x -> colors.blue ^^ x ^^ colors.default) names in
      let names = separate (string ", ") names in
      names
    else
      colors.red ^^ string "[no name]" ^^ colors.default
  ;;

  let pnames buf (env, names) =
    pdoc buf (print_names env, names)
  ;;

  let pname buf (env, point) =
    pdoc buf ((fun () -> print_var env (get_name env point)), ())
  ;;

  let print_exports (env, mname) =
    let exports = List.map (fun x -> utf8string (Variable.print (fst3 x))) (get_exports env mname) in
    separate (string ", ") exports
  ;;

  let pexports buf env =
    pdoc buf (print_exports, env)
  ;;

  internal_pnames := pnames;;

  let rec print_quantified
      (env: env)
      (q: string)
      (name: name)
      (kind: SurfaceSyntax.kind)
      (typ: typ) =
    utf8string q ^^ lparen ^^ print_var env name ^^ space ^^ colon ^^ space ^^
    print_kind kind ^^ rparen ^^ dot ^^ jump (print_type env typ)

  and print_point env point =
    try
      if is_flexible env point then
        print_var env (get_name env point) ^^ star
      else if internal_wasflexible point then
          lparen ^^ string "inst→" ^^ print_type env (modulo_flex_v env point) ^^ rparen
      else
        print_var env (get_name env point)
    with UnboundPoint ->
      colors.red ^^ string "!! ☠ !!" ^^ colors.default


  (* TEMPORARY this does not respect precedence and won't insert parentheses at
   * all! *)
  and print_type env = function
    | TyUnknown ->
        string "unknown"

    | TyDynamic ->
        string "dynamic"

    | TyOpen point ->
        print_point env point

    | TyBound i ->
        int i
        (* Log.error "All variables should've been bound at this stage" *)

      (* Special-casing *)
    | TyAnchoredPermission (TyOpen p, TySingleton (TyOpen p')) ->
        let star = if is_flexible env p then star else empty in
        let star' = if is_flexible env p' then star else empty in
        print_names env (get_names env p) ^^ star ^^ space ^^ equals ^^ space ^^
        print_names env (get_names env p') ^^ star'

    | (TyForall _) as t ->
        let rec strip_bind acc env = function
          | TyForall ((binding, _), t) ->
              let env, t, _ = bind_rigid_in_type env binding t in
              strip_bind (binding :: acc) env t
          | _ as t ->
              List.rev acc, env, t
        in
        let vars, env, t = strip_bind [] env t in
        let vars = List.map (fun (x, k, _) ->
          if k = KType then
            print_var env x
          else
            print_var env x ^^ space ^^ colon ^^ space ^^ print_kind k
        ) vars in
        let vars = separate (comma ^^ space) vars in
        let vars = lbracket ^^ vars ^^ rbracket in
        vars ^//^ print_type env t

    | TyExists ((name, kind, _) as binding, typ) ->
        let env, typ, _ = bind_rigid_in_type env binding typ in
        print_quantified env "∃" name kind typ

    | TyApp (t1, t2) ->
        print_type env t1 ^^ space ^^ separate_map space (print_type env) t2

    | TyTuple components ->
        lparen ^^
        separate_map
          (comma ^^ space)
          (print_type env) components ^^
        rparen

    | TyConcreteUnfolded (name, fields, clause) ->
        print_data_type_def_branch env (snd name) fields clause

      (* Singleton types. *)
    | TySingleton typ ->
        equals ^^ print_type env typ

      (* Function types. *)
    | TyArrow (t1, t2) ->
        prefix 0 1
          (print_type env t1 ^^ space ^^ arrow)
          (print_type env t2)

      (* Permissions. *)
    | TyAnchoredPermission (t1, t2) ->
        print_type env t1 ^^ space ^^ at ^^ space ^^ print_type env t2

    | TyEmpty ->
        string "empty"

    | TyStar (t1, t2) ->
        prefix 0 1
          (print_type env t1 ^^ space ^^ string "∗")
          (print_type env t2)

    | TyBar (p, q) ->
        lparen ^^ print_type env p ^^ space ^^ bar ^^ space ^^
        print_type env q ^^ rparen

    | TyAnd (constraints, t) ->
        let constraints = print_constraints env constraints in
        lparen ^^ constraints ^^ rparen ^^ space ^^ string "∧" ^^ space ^^
        print_type env t

    | TyImply (constraints, t) ->
        let constraints = print_constraints env constraints in
        lparen ^^ constraints ^^ rparen ^^ space ^^ string "=>" ^^ space ^^
        print_type env t

  and print_constraints env constraints =
    let constraints = List.map (fun (f, t) ->
      print_data_type_flag f ^^ space ^^ print_type env t
    ) constraints in
    let constraints = separate comma constraints in
    constraints

  and print_data_field_def env = function
    | FieldValue (name, typ) ->
        print_field_name name ^^ colon ^^ jump (print_type env typ)

    | FieldPermission typ ->
        string "permission" ^^ space ^^ print_type env typ

  and print_data_type_def_branch env (name: Datacon.name) fields clause =
    let record =
      if List.length fields > 0 then
        space ^^ lbrace ^^
        nest 4
          (break 1 ^^ separate_map
            (semi ^^ break 1)
            (print_data_field_def env) fields) ^^
        nest 2 (break 1 ^^ rbrace)
      else
        empty
    in
    let clause =
      if equal env ty_bottom clause then
        empty
      else
        space ^^ string "adopts" ^^ space ^^ print_type env clause
    in
    print_datacon name ^^ record ^^ clause

  and print_data_type_flag = function
    | SurfaceSyntax.Exclusive ->
        string "exclusive"
    | SurfaceSyntax.Duplicable ->
        string "duplicable"
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let print_fact (fact: fact): document =
    match fact with
    | Duplicable bitmap ->
        lbracket ^^
        separate_map
          empty
          (fun b -> if b then string "x" else string "-") (Array.to_list bitmap) ^^
        rbracket
    | Exclusive ->
        string "exclusive"
    | Affine ->
        string "affine"
    | Fuzzy i ->
        string "fuzzy " ^^ int i
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let pfact buf (fact: fact) =
    pdoc buf (print_fact, fact)
  ;;

  internal_pfact := pfact;;

  let print_facts (env: env): document =
    let is name is_abstract ?params w =
      let params =
        match params with
        | Some params -> concat_map (fun param -> space ^^ utf8string param) params
        | None -> empty
      in
      colors.underline ^^ print_var env name ^^ params ^^
      colors.default ^^ string " is " ^^
      (if is_abstract then string "abstract and " else empty) ^^
      utf8string w
    in
    let print_fact name is_abstract arity fact =
      let params = MzPprint.name_gen arity in
      let is w = is name is_abstract ~params w in
      match fact with
      | Fuzzy _ ->
          is "fuzzy"
      | Exclusive ->
          is "exclusive"
      | Affine ->
          is "affine"
      | Duplicable bitmap ->
          let dup_params = List.map2
            (fun b param -> if b then Some param else None)
            (Array.to_list bitmap)
            params
          in
          let dup_params = MzList.filter_some dup_params in
          if List.length dup_params > 0 then begin
            let verb = string (if List.length dup_params > 1 then " are " else " is ") in
            let dup_params = List.map utf8string dup_params in
            is "duplicable if " ^^ english_join dup_params ^^ verb ^^
            string "duplicable"
          end else begin
            is "duplicable"
          end
    in
    let lines =
      fold_definitions env (fun acc var definition ->
        let fact = get_fact env var in
        let kind = get_kind env var in
        let name = get_name env var in
        let arity = get_arity_for_kind kind in
        let is_abstract = (fst definition = None) in
        print_fact name is_abstract arity fact :: acc
      ) []
    in
    separate hardline lines
  ;;

  let print_permission_list (env, permissions): document =
    if List.length permissions > 0 then
      let permissions = List.map (print_type env) permissions in
      separate (comma ^^ space) permissions
    else
      string "unknown"
  ;;

  let ppermission_list buf (env, point) =
    let permissions = get_permissions env point in
    pdoc buf (print_permission_list, (env, permissions))
  ;;

  let print_permissions (env: env): document =
    let mkheader str =
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let header =
      let str = "PERMISSIONS:" ^
        (if is_inconsistent env then " ⚠ inconsistent ⚠" else "")
      in
      mkheader str
    in
    let lines = fold_terms env (fun acc var permissions ->
      let names = get_names env var in
      if List.exists (function
        | User (mname, _) when not (Module.equal (module_name env) mname) ->
            true
        | _ ->
            false
      ) names then
        empty :: acc
      else
        let names = print_names env names in
        let perms = print_permission_list (env, permissions) in
        (names ^^ space ^^ at ^^ space ^^ (nest 2 perms)) :: acc
    ) [] in
    let lines = List.rev lines in
    let lines = List.filter ((<>) empty) lines in
    let lines = separate (break 1) lines in
    (* Now print floating permissions. *)
    let fp_header = mkheader "FLOATING:" in
    let fp_lines =
      List.map (print_type env) (get_floating_permissions env)
    in
    let fp_lines = separate (break 1) fp_lines in
    header ^^ (nest 2 (break 1 ^^ lines)) ^^ hardline ^^
    fp_header ^^ (nest 2 (break 1 ^^ fp_lines))
  ;;

  let ppermissions buf permissions =
    pdoc buf (print_permissions, permissions)
  ;;

  internal_ppermissions := ppermissions;;

  let ptype buf arg =
    pdoc buf ((fun (env, t) -> print_type env t), arg)
  ;;

  let penv buf (env: env) =
    pdoc buf (print_permissions, env)
  ;;

  internal_ptype := ptype;;

  let pconstraints buf (env, constraints) =
    pdoc buf ((fun () -> print_constraints env constraints), ())
  ;;

  let print_binders (env: env): document =
    utf8string "Γ (unordered) = " ^^
    separate
      (semi ^^ space)
      (map env (fun var -> separate_map (string " = ") (print_var env) (get_names env var)))
  ;;


end
