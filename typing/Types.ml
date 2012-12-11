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

include TypeCore
include DeBruijn


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
let (!!) = function TyPoint x -> x | _ -> assert false;;
let ( !* ) = Lazy.force;;
let (>>=) = Option.bind;;
let (|||) o1 o2 = if Option.is_some o1 then o1 else o2 ;;
let fst3 (x, _, _) = x;;
let snd3 (_, x, _) = x;;
let thd3 (_, _, x) = x;;


let (!!=) = function
  | TySingleton (TyPoint x) ->
      x
  | _ ->
      assert false
;;

let ty_equals x =
  TySingleton (TyPoint x)
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
    TyVar 0
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


let rec flatten_star p =
  match p with
  | TyStar (p, q) ->
      flatten_star p @ flatten_star q
  | TyEmpty ->
      []
  | TyPoint _
  | TyVar _
  | TyAnchoredPermission _ as p ->
      [p]
  | _ ->
      Log.error "[flatten_star] only works for types with kind PERM"
;;

let fold_star perms =
  if List.length perms > 0 then
    Hml_List.reduce (fun acc x -> TyStar (acc, x)) perms
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

(* Dealing with floating permissions. *)

let sub_floating_permission env p =
  match Hml_List.take_bool (same env p) env.floating_permissions with
  | Some (perms, _) ->
      Some { env with floating_permissions = perms }
  | None ->
      None
;;

let add_floating_permission env p =
  { env with floating_permissions = p :: env.floating_permissions }
;;


(* -------------------------------------------------------------------------- *)

(* Various functions related to binding and finding. *)

let head name location ?(flexible=false) kind =
  let structure = if flexible then Flexible None else Rigid in
  {
    names = [name];
    locations = [location];
    binding_mark = Mark.create ();
    structure;
    kind;
  }
;;

let initial_permissions_for_point point =
  [ ty_equals point; TyUnknown ]
;;

let bind_term
    (env: env)
    (name: name)
    (location: location)
    ?flexible
    (ghost: bool): env * point
  =
  let binding =
    head name location ?flexible KTerm,
    BTerm { permissions = []; ghost }
  in
  let point, state = PersistentUnionFind.create binding env.state in
  let initial_permissions = initial_permissions_for_point point in
  let state = PersistentUnionFind.update
    (function
      | (head, BTerm raw) -> head, BTerm { raw with permissions = initial_permissions }
      | _ -> assert false)
    point
    state
  in
  { env with state }, point
;;

let bind_type
    (env: env)
    (name: name)
    (location: location)
    ?flexible
    ?(definition: type_def option)
    (fact: fact)
    (kind: kind): env * point
  =
  let return_kind, _args = flatten_kind kind in
  Log.check (return_kind = KType || return_kind = KPerm)
    "[bind_type] is for variables with kind TYPE or PERM only";
  let binding = head name location ?flexible kind, BType { fact; definition; } in
  let point, state = PersistentUnionFind.create binding env.state in
  { env with state }, point
;;

(* [fact] is unused if it's a [KTerm] variable... *)
let bind_var (env: env) ?flexible ?(fact=Affine) (name, kind, location: type_binding): env * point =
  match kind with
    | KType ->
        (* Of course, such a type variable does not have a definition. *)
        bind_type env name location ?flexible fact kind
    | KTerm ->
        (* This is wrong because we're floating "real" parameters of a function
           as type variables with kind TERM, so it's not a ghost variable... *)
        bind_term env name location ?flexible true
    | KPerm ->
        bind_type env name location ?flexible fact kind
    | KArrow _ ->
        Log.error "No arrows expected here"
;;

(* When crossing a binder, say, [a :: TYPE], use this function to properly add
 * [a] in scope. *)
let bind_var_in_type2
    (env: env)
    (binding: type_binding)
    ?flexible
    (typ: typ): env * typ * point
  =
  let env, point = bind_var env ?flexible binding in
  let typ = tsubst (TyPoint point) 0 typ in
  env, typ, point
;;

let bind_var_in_type
    (env: env)
    (binding: type_binding)
    ?flexible
    (typ: typ): env * typ
  =
  let env, typ, _ = bind_var_in_type2 env binding ?flexible typ in
  env, typ
;;

(* ---------------------------------------------------------------------------- *)

let find_type (env: env) (point: point): name * type_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, BType binding ->
      List.hd names, binding
  | _ ->
      Log.error "Binder %a is not a type" !internal_pnames (env, get_names env point)
;;

let find_term (env: env) (point: point): name * term_binder =
  match PersistentUnionFind.find point env.state with
  | { names; _ }, BTerm binding ->
      List.hd names, binding
  | _ ->
      Log.error "Binder %a is not a term" !internal_pnames (env, get_names env point)
;;

let is_type (env: env) (point: point): bool =
  match PersistentUnionFind.find point env.state with
  | _, BType _ ->
      true
  | _ ->
      false
;;

let is_term (env: env) (point: point): bool =
  match PersistentUnionFind.find point env.state with
  | _, BTerm _ ->
      true
  | _ ->
      false
;;

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

let map_types env f =
  Hml_List.filter_some
    (List.rev
      (PersistentUnionFind.fold
        (fun acc _k -> function
          | (head, BType b) -> Some (f head b) :: acc
          | _ -> None :: acc)
        [] env.state))
;;

let map_terms env f =
  Hml_List.filter_some
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

let fold env f acc =
  PersistentUnionFind.fold (fun acc k v ->
    f acc k v)
  acc env.state
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
;;

let refresh_fact env p fact =
  replace_type env p (fun binder -> { binder with fact })
;;


(* ---------------------------------------------------------------------------- *)

(* Interface-related functions. *)

(* Get all the names from module [mname] found in [env]. *)
let get_exports env mname =
  let assoc =
    fold env (fun acc point ({ names; kind; _ }, _) ->
      let canonical_names = Hml_List.map_some (function
        | User (m, x) when Module.equal m mname ->
            Some (x, kind)
        | _ ->
            None
      ) names in
      List.map (fun (x, k) -> x, k, point) canonical_names :: acc
    ) []
  in
  List.flatten assoc
;;

(* ---------------------------------------------------------------------------- *)

(* Dealing with marks. *)

let is_marked (env: env) (point: point): bool =
  let { binding_mark; _ }, _ = PersistentUnionFind.find point env.state in
  Mark.equals binding_mark env.mark
;;

let mark (env: env) (point: point): env =
  { env with state =
      PersistentUnionFind.update (fun (head, binding) ->
        { head with binding_mark = env.mark }, binding
      ) point env.state
  }
;;

let refresh_mark (env: env): env =
  { env with mark = Mark.create () }
;;


(* ---------------------------------------------------------------------------- *)

(* A hodge-podge of getters. *)

let get_name env p =
  let names = get_names env p in
  try
    List.find (function User _ -> true | Auto _ -> false) names
  with Not_found ->
    List.hd names
;;

let get_permissions (env: env) (point: point): permissions =
  let _, { permissions; _ } = find_term env point in
  permissions
;;

let get_fact (env: env) (point: point): fact =
  let _, { fact; _ } = find_type env point in
  fact
;;

let get_locations (env: env) (point: point): location list =
  match PersistentUnionFind.find point env.state with
  | { locations; _ }, _ ->
      locations
;;

let get_location env p =
  List.hd (get_locations env p)
;;

let get_definition (env: env) (point: point): type_def option =
  let _, { definition; _ } = find_type env point in
  definition
;;

let get_adopts_clause env point: adopts_clause =
  match get_definition env point with
  | Some (Some (_, _, clause), _) ->
      clause
  | _ ->
      Log.error "This is not a concrete data type."
;;

let get_branches env point: data_type_def_branch list =
  match get_definition env point with
  | Some (Some (_, branches, _), _) ->
      branches
  | _ ->
      Log.error "This is not a concrete data type."
;;

let get_arity (env: env) (point: point): int =
  get_arity_for_kind (get_kind env point)
;;

let get_variance (env: env) (point: point): variance list =
  match get_definition env point with
  | Some (_, v) ->
      v
  | None ->
      assert false
;;

let def_for_datacon (env: env) (datacon: Datacon.name): SurfaceSyntax.data_type_flag * data_type_def * adopts_clause=
  match DataconMap.find_opt datacon env.type_for_datacon with
  | Some point ->
      let def, _ = Option.extract (get_definition env point) in
      Option.extract def
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let type_for_datacon (env: env) (datacon: Datacon.name): point =
  DataconMap.find datacon env.type_for_datacon
;;

let variance env point i =
  let _, { definition; _ } = find_type env point in
  let variance = snd (Option.extract definition) in
  List.nth variance i
;;


(* ---------------------------------------------------------------------------- *)

(* What type am I dealing with? *)

let is_flexible (env: env) (point: point): bool =
  match PersistentUnionFind.find point env.state with
  | { structure = Flexible None; _ }, _ ->
      true
  | _ ->
      false
;;

let has_definition (env: env) (point: point): bool =
  match get_definition env point with
  | Some (Some _, _) ->
      true
  | _ ->
      false
;;


(* ---------------------------------------------------------------------------- *)

(* Instantiating. *)

let instantiate_flexible env p t =
  Log.check (is_flexible env p) "Trying to instantiate a variable that's not flexible";
  Log.debug "Instantiating %a with %a"
    !internal_pnames (env, get_names env p)
    !internal_ptype (env, t);
  match t with
  | TyPoint p' ->
      merge_left env p' p
  | _ ->
      { env with state =
          PersistentUnionFind.update (function
            | head, binding ->
                { head with structure = Flexible (Some t) }, binding
          ) p env.state }
;;

let instantiate_adopts_clause clause args =
  let clause = Option.map_none ty_bottom clause in
  let args = List.rev args in
  Hml_List.fold_lefti (fun i clause arg -> tsubst arg i clause) clause args
;;

let instantiate_branch branch args =
  let args = List.rev args in
  let branch = Hml_List.fold_lefti (fun i branch arg ->
    tsubst_data_type_def_branch arg i branch) branch args
  in
  branch
;;

let find_and_instantiate_branch
    (env: env)
    (point: point)
    (datacon: Datacon.name)
    (args: typ list) =
  let branch =
    List.find
      (fun (datacon', _) -> Datacon.equal datacon datacon')
      (get_branches env point)
  in
  let dc, fields = instantiate_branch branch args in
  let clause = instantiate_adopts_clause (get_adopts_clause env point) args in
  dc, fields, clause
;;

(* Misc. *)

let point_by_name (env: env) ?(mname: Module.name option) (name: Variable.name): point =
  let mname = Option.map_none env.module_name mname in
  let module T = struct exception Found of point end in
  try
    fold env (fun () point ({ names; _ }, _binding) ->
      if List.exists (names_equal (User (mname, name))) names then
        raise (T.Found point)) ();
    raise Not_found
  with T.Found point ->
    point
;;

(** This function is actually fairly ugly. This is a temporary solution so that
    [TypeChecker] as well as the test files can refer to type constructors
    defined in the file (e.g. int), for type-checking arithmetic expressions, for
    instance... *)
let find_type_by_name env ?mname name =
  let name = Variable.register name in
  let mname = Option.map Module.register mname in
  TyPoint (point_by_name env ?mname name)
;;

let is_tyapp = function
  | TyPoint p ->
      Some (p, [])
  | TyApp (p, args) ->
      Some ((match p with
        | TyPoint p ->
            p
        | _ ->
            assert false), args)
  | _ ->
      None
;;

let make_datacon_letters env kind flexible f =
  let _return_kind, arg_kinds = flatten_kind kind in
  (* Turn the list of parameters into letters *)
  let letters: string list = Hml_Pprint.name_gen (List.length arg_kinds) in
  let env, points = Hml_List.fold_left2i (fun i (env, points) kind letter ->
    let env, point =
      let letter = Auto (Variable.register letter) in
      bind_var env ~flexible ~fact:(f i) (letter, kind, env.location)
    in
    env, point :: points) (env, []) arg_kinds letters
  in
  let points = List.rev points in
  env, points
;;

let bind_datacon_parameters (env: env) (kind: kind) (branches: data_type_def_branch list) (clause: adopts_clause):
    env * point list * data_type_def_branch list * adopts_clause =
  let env, points = make_datacon_letters env kind false (fun i -> Fuzzy i) in
  let arity = get_arity_for_kind kind in
  let branches, clause = Hml_List.fold_lefti (fun i (branches, clause) point ->
    let index = arity - i - 1 in
    let branches = List.map (tsubst_data_type_def_branch (TyPoint point) index) branches in
    let clause = Option.map (tsubst (TyPoint point) index) clause in
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
          TyConcreteUnfolded (dc, fields, clause)
      | _ ->
        t
      end
  | None ->
      t
;;


(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  let tfold = fold;;

  open Hml_Pprint

  let fold = tfold;;

  (* If [f arg] returns a [document], then write [Log.debug "%a" pdoc (f, arg)] *)
  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    PpBuffer.pretty 1.0 Bash.twidth buf (f env)
  ;;

  (* --------------------------------------------------------------------------- *)

  let print_var env = function
    | User (m, var) when Module.equal env.module_name m ->
        print_string (Variable.print var)
    | User (m, var) ->
        print_string (Module.print m) ^^ ccolon ^^ print_string (Variable.print var)
    | Auto var ->
        colors.yellow ^^ print_string (Variable.print var) ^^ colors.default
  ;;

  let pvar buf (env, var) =
    pdoc buf (print_var env, var)
  ;;

  let print_datacon datacon =
    print_string (Datacon.print datacon)
  ;;

  let print_field field =
    print_string (Field.print field)
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
      let names = join (string ", ") names in
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

  let print_exports env =
    let exports = 
      fold env (fun acc point ({ names; kind; _ }, _) ->
        ignore (kind, point);
        let names = Hml_List.map_some (function
          | User (m, x) ->
              Some (m, x)
          | _ ->
              None
        ) names in
        let names = List.map (fun (m, x) ->
          print_string (Module.print m) ^^ ccolon ^^ print_string (Variable.print x)
        ) names in
        (join (string " = ") names) :: acc
      ) []
    in
    join (string ", ") exports
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
    print_string q ^^ lparen ^^ print_var env name ^^ space ^^ ccolon ^^ space ^^
    print_kind kind ^^ rparen ^^ dot ^^ jump (print_type env typ)

  and print_point env point =
    match structure env point with
    | Some t ->
        lparen ^^ string "flex→" ^^ print_type env t ^^ rparen
    | _ ->
        if is_flexible env point then
          print_var env (get_name env point) ^^ star
        else
          print_var env (get_name env point)


  (* TEMPORARY this does not respect precedence and won't insert parentheses at
   * all! *)
  and print_type env = function
    | TyUnknown ->
        string "unknown"

    | TyDynamic ->
        string "dynamic"

    | TyPoint point ->
        print_point env point

    | TyVar i ->
        int i
        (* Log.error "All variables should've been bound at this stage" *)

      (* Special-casing *)
    | TyAnchoredPermission (TyPoint p, TySingleton (TyPoint p')) ->
        let star = if is_flexible env p then star else empty in
        let star' = if is_flexible env p' then star else empty in
        print_names env (get_names env p) ^^ star ^^ space ^^ equals ^^ space ^^
        print_names env (get_names env p') ^^ star'

    | (TyForall _) as t ->
        let rec strip_bind acc env = function
          | TyForall ((binding, _), t) ->
              let env, t = bind_var_in_type env binding t in
              strip_bind (binding :: acc) env t
          | _ as t ->
              List.rev acc, env, t
        in
        let vars, env, t = strip_bind [] env t in
        let vars = List.map (fun (x, k, _) ->
          if k = KType then
            print_var env x
          else
            print_var env x ^^ space ^^ colon ^^ colon ^^ space ^^ print_kind k
        ) vars in
        let vars = join (comma ^^ space) vars in
        let vars = lbracket ^^ vars ^^ rbracket in
        vars ^^ space ^^ print_type env t

    | TyExists ((name, kind, _) as binding, typ) ->
        let env, typ = bind_var_in_type env binding typ in
        print_quantified env "∃" name kind typ

    | TyApp (t1, t2) ->
        print_type env t1 ^^ space ^^ join space (List.map (print_type env) t2)

    | TyTuple components ->
        lparen ^^
        join
          (comma ^^ space)
          (List.map (print_type env) components) ^^
        rparen

    | TyConcreteUnfolded (name, fields, clause) ->
        print_data_type_def_branch env name fields clause

      (* Singleton types. *)
    | TySingleton typ ->
        equals ^^ print_type env typ

      (* Function types. *)
    | TyArrow (t1, t2) ->
        print_type env t1 ^^ space ^^ arrow ^^
        group (break1 ^^ print_type env t2)

      (* Permissions. *)
    | TyAnchoredPermission (t1, t2) ->
        print_type env t1 ^^ space ^^ at ^^ space ^^ print_type env t2

    | TyEmpty ->
        string "empty"

    | TyStar (t1, t2) ->
        print_type env t1 ^^ space ^^ string "∗" ^^ space ^^ print_type env t2

    | TyBar (p, q) ->
        lparen ^^ print_type env p ^^ space ^^ bar ^^ space ^^
        print_type env q ^^ rparen

    | TyConstraints (constraints, t) ->
        let constraints = List.map (fun (f, t) ->
          print_data_type_flag f ^^ space ^^ print_type env t
        ) constraints in
        let constraints = join comma constraints in
        lparen ^^ constraints ^^ rparen ^^ space ^^ equals ^^ rangle ^^ space ^^
        print_type env t

  and print_data_field_def env = function
    | FieldValue (name, typ) ->
        print_field name ^^ colon ^^ jump (print_type env typ)

    | FieldPermission typ ->
        string "permission" ^^ space ^^ print_type env typ

  and print_data_type_def_branch env name fields clause =
    let record =
      if List.length fields > 0 then
        space ^^ lbrace ^^
        nest 4
          (break1 ^^ join
            (semi ^^ break1)
            (List.map (print_data_field_def env) fields)) ^^
        nest 2 (break1 ^^ rbrace)
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
        join
          empty
          ((List.map (fun b -> if b then string "x" else string "-")) (Array.to_list bitmap)) ^^
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

  let print_facts (env: env): document =
    let is name is_abstract ?params w =
      let params =
        match params with
        | Some params -> join_left space (List.map print_string params)
        | None -> empty
      in
      colors.underline ^^ print_var env name ^^ params ^^
      colors.default ^^ string " is " ^^
      (if is_abstract then string "abstract and " else empty) ^^
      print_string w
    in
    let print_fact name is_abstract arity fact =
      let params = Hml_Pprint.name_gen arity in
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
          let dup_params = Hml_List.filter_some dup_params in
          if List.length dup_params > 0 then begin
            let verb = string (if List.length dup_params > 1 then " are " else " is ") in
            let dup_params = List.map print_string dup_params in
            is "duplicable if " ^^ english_join dup_params ^^ verb ^^
            string "duplicable"
          end else begin
            is "duplicable"
          end
    in
    let lines =
      map_types env (fun { names; kind; _ } { definition; fact; _ } ->
        let name = List.hd names in
        let arity = get_arity_for_kind kind in
        match definition with
        | Some _ ->
            print_fact name false arity fact
        | None ->
            print_fact name true arity fact
      )
    in
    join hardline lines
  ;;

  let print_permission_list (env, { permissions; _ }): document =
    (* let permissions = List.filter (function
      TySingleton (TyPoint _) -> false | _ -> true
    ) permissions in *)
    if List.length permissions > 0 then
      let permissions = List.map (print_type env) permissions in
      join (comma ^^ space) permissions
    else
      string "unknown"
  ;;

  let ppermission_list buf (env, point) =
    let _, binder = find_term env point in
    pdoc buf (print_permission_list, (env, binder))
  ;;

  let print_permissions (env: env): document =
    let header =
      let str = "PERMISSIONS:" ^
        (if env.inconsistent then " ⚠ inconsistent ⚠" else "")
      in
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let lines = map_terms env (fun { names; _ } binder ->
      if List.exists (function
        | User (mname, _) when not (Module.equal env.module_name mname) ->
            true
        | _ ->
            false
      ) names then
        empty
      else
        let names = print_names env names in
        let perms = print_permission_list (env, binder) in
        names ^^ space ^^ at ^^ space ^^ (nest 2 perms)
    ) in
    let lines = List.filter ((<>) empty) lines in
    let lines = join break1 lines in
    header ^^ (nest 2 (break1 ^^ lines))
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

  let print_binders (env: env): document =
    print_string "Γ (unordered) = " ^^
    join
      (semi ^^ space)
      (map env (fun names _ -> join (string " = ") (List.map (print_var env) names)))
  ;;


end
