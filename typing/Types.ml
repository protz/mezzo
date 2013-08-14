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

open Kind
open TypeCore
open DeBruijn

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
  | _ as t -> Log.error "Not a TyOpen %a" !internal_ptype (empty_env, t)
;;

let ( !!= )       = function
  | TySingleton (TyOpen x) ->
      x
  | _ as t ->
      Log.error "Not a ty_equals %a" !internal_ptype (empty_env, t)
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

let ty_open v =
  TyOpen v
;;

let fold_star perms =
  if List.length perms > 0 then
    MzList.reduce (fun acc x -> TyStar (acc, x)) perms
  else
    TyEmpty
;;

let strip_quantifiers_and_bind env q t =
  let rec strip acc env t =
    match t with
    | TyQ (q', binding, _, t) when q = q' ->
        let env, t, _ = bind_rigid_in_type env binding t in
        strip (binding :: acc) env t
    | _ ->
        List.rev acc, env, t
  in
  strip [] env t

let fold_quantifier q bindings t =
  List.fold_right (fun (binding, flavor) t ->
    TyQ (q, binding, flavor, t)
  ) bindings t
;;

let fold_forall =
  fold_quantifier Forall

let fold_exists =
  fold_quantifier Exists

let fresh_auto_name prefix = Auto (Utils.fresh_var prefix);;



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

let get_location env p =
  List.hd (get_locations env p)
;;

(* TEMPORARY when giving, we should compute a meet; when taking, we should
   compute a join. *)
let get_adopts_clause env point: typ =
  match get_definition env point with
  | Some (Concrete ts) ->
      let branches = List.map find_branch ts in
      (* The [adopts] clause is now per-branch, instead of per-data-type.
        We should in principle return the meet of the [adopts] clauses
        of all branches. However, the surface language imposes that
        all branches have the same [adopts] clause, except perhaps some
        branches which are immutable and don't have an adopts clause.
        In that setting, the meet is easy to compute. *)
      let meet ty1 branch2 =
        let ty2 = branch2.branch_adopts in
        match ty1, is_non_bottom ty2 with
        | TyUnknown, _ ->
            ty2
        | _, None ->
            (* [ty2] is bottom *)
            ty2
        | _, Some _ ->
            (* [ty2] is non-bottom *)
            assert (equal env ty1 ty2);
            ty2
      in
      List.fold_left meet TyUnknown branches
  | _ ->
      (* An abstract type / type abbreviation has no adopts clause (as of now). *)
      ty_bottom
;;

let is_tyopen = function
  | TyOpen _ -> true
  | _ -> false
;;

let get_branches env point: typ list =
  match get_definition env point with
  | Some (Concrete branches) ->
      branches
  | _ ->
      Log.error "This is not a concrete data type."
;;

let get_arity (env: env) (var: var): int =
  Kind.arity (get_kind env var)
;;

let rec get_kind_for_type env t =
  match modulo_flex env t with
  | TyBound _ ->
      Log.error "No free variables"
  | TyOpen p ->
      get_kind env p

  | TyQ (_, binding, _, t) ->
      let env, t, _ = bind_rigid_in_type env binding t in
      get_kind_for_type env t

  | TyApp (p, _) ->
      let _, return_kind = Kind.as_arrow (get_kind env !!p) in
      return_kind

  | TyUnknown
  | TyDynamic
  | TySingleton _
  | TyArrow _
  | TyBar _
  | TyTuple _
  | TyConcrete _ ->
      KType

  | TyAnchoredPermission _
  | TyEmpty
  | TyStar _ ->
      KPerm

  | TyAnd (_, t) ->
      get_kind_for_type env t
;;


let branches_for_datacon env (t, _dc) =
  get_branches env !!t
;;

let branches_for_branch env (branch : branch) : typ list =
  get_branches env !!(fst branch.branch_datacon)
;;

let branch_for_datacon env (typ, datacon) : typ =
  let branches = get_branches env !!typ in
  List.find (fun t' ->
    let branch' = find_branch t' in
    Datacon.equal datacon (snd branch'.branch_datacon)
  ) branches
;;

let fields_for_datacon env dc : Field.name list =
  let branch = branch_for_datacon env dc in
  let branch = find_branch branch in
  List.map fst branch.branch_fields
;;

let flavor_for_datacon env dc =
  let branch = branch_for_datacon env dc in
  let branch = find_branch branch in
  branch.branch_flavor
;;

let variance env var i =
  let variance = get_variance env var in
  List.nth variance i
;;

(* ---------------------------------------------------------------------------- *)

(* Instantiating. *)

let instantiate_type t args =
  let args = List.rev args in
  MzList.fold_lefti (fun i t arg -> tsubst arg i t) t args
;;

let find_and_instantiate_branch
    (env: env)
    (var: var)
    (datacon: Datacon.name)
    (args: typ list) : typ =
  let branch = branch_for_datacon env (TyOpen var, datacon) in
  instantiate_type branch args
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

let is_abbrev env v =
  match get_definition env v with
  | Some (Abbrev _) ->
      true
  | _ -> false
;;

let assert_concrete t =
  match t with TyConcrete b -> b | _ -> assert false;;

let is_concrete t =
  match t with TyConcrete _ -> true | _ -> false;;

let is_term env v = (get_kind env v = KTerm);;
let is_perm env v = (get_kind env v = KPerm);;
let is_type env v = (snd (Kind.as_arrow (get_kind env v)) = KType);;

(* ---------------------------------------------------------------------------- *)

(*  Various transformations on types. *)

(** [collect t] recursively walks down a type with kind KType, extracts all
    the permissions that appear in it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    KPerm, which represents all the permissions that were just extracted. *)

(** In fact, [collect] also calls itself recursively at kind KPerm, and
    is able to extract permissions out of permissions, e.g., to find a
    TyBar nested inside a TyAnchoredPermission. Because this behavior was
    not documented, I thought it was not essential, but it fact it is. *)

class collect (perms : typ list ref) = object (self)
  inherit [unit] map as super
  (* We re-implement the main visitor method in order to be warned
     about new cases and to share code for some cases. *)
  method! visit () ty =
    (* TEMPORARY No call to [modulo_flex]; is this normal? *)
    match ty with

      (* We stop at the following constructors. *)

    | TyUnknown
    | TyDynamic
    | TyBound _
    | TyOpen _
    | TyQ _
    | TyApp _
    | TySingleton _
    | TyArrow _
    | TyEmpty
      -> ty

      (* We descend into the following constructs. *)

    | TyTuple _
    | TyConcrete _
    | TyStar _
      -> super#visit () ty

      (* We descend into the right-hand side of [TyAnd] and [TyAnchoredPermission]. *)

    | TyAnd (c, ty) ->
        TyAnd (c, self#visit () ty)
    | TyAnchoredPermission (x, p) ->
        TyAnchoredPermission (x, self#visit () p)

      (* [TyBar] is where the action takes place. *)

    | TyBar (ty, p) ->
        let p = self#visit () p in
       perms := p :: !perms;
       self#visit () ty

  (* At [TyConcrete], we set aside the [FieldPermission]s and
     descend into the [FieldValue]s. *)
  method! branch () branch =
    { 
      branch_flavor = branch.branch_flavor;
      (* Nothing to collect here. *)
      branch_datacon = branch.branch_datacon;
      branch_fields = List.map (self#field ()) branch.branch_fields;
      branch_adopts = branch.branch_adopts;
    }

end

let collect (ty : typ) : typ * typ list =
  let perms = ref [] in
  let ty = (new collect perms) # visit () ty in
  ty, !perms

class mark (env : env ref) = object (self)
  inherit [unit] iter
  method! normalize () ty =
    modulo_flex !env ty
  (* Mark a variable [v], and if [v] is newly marked, find the permissions
     for [v] in the environment and follow. *)
  method! tyopen () v =
    if not (is_marked !env v) then begin
      env := mark !env v;
      if is_term !env v then begin
        let permissions = get_permissions !env v in
        List.iter (self#visit ()) permissions
      end
    end
  (* Do not descend into arrows. (Why?) *)
  method! tyarrow () _ty1 _ty2 =
    ()
end

let mark_reachable (env : env) (ty : typ) : env =
  let env = ref env in
  (new mark env) # visit () ty;
  !env

(* ---------------------------------------------------------------------------- *)


let make_datacon_letters env kind flexible =
  let arg_kinds, _return_kind = Kind.as_arrow kind in
  (* Turn the list of parameters into letters *)
  let letters: string list = MzPprint.name_gen (List.length arg_kinds) in
  let env, vars = List.fold_left2 (fun (env, vars) kind letter ->
    let env, var =
      let letter = Auto (Variable.register letter) in
      if flexible then
       bind_flexible env (letter, kind, location env)
      else
       bind_rigid env (letter, kind, location env)
    in
    env, var :: vars) (env, []) arg_kinds letters
  in
  let vars = List.rev vars in
  env, vars
;;

let bind_datacon_parameters (env: env) (kind: kind) (branches: typ list):
    env * var list * typ list =
  let env, points = make_datacon_letters env kind false in
  let arity = Kind.arity kind in
  let branches = MzList.fold_lefti (fun i branches point ->
    let index = arity - i - 1 in
    let branches = List.map (tsubst (TyOpen point) index) branches in
    branches
  ) branches points in
  env, points, branches
;;

let rec expand_if_one_branch (env: env) (t: typ) =
  (* Having [FieldPermission] was a mistake... because almost no single place in
   * the code is able to deal with [FieldPermission]s, we must make sure
   * everytime a nominal type turns into a branch, we collect the permissions
   * and rewrap everything in a [TyBar] (which the code handles well). *)
  let wrap_if t =
    let t, p = collect t in
    if List.length p > 0 then
      if get_kind_for_type env t = KPerm then
        TyStar (t, fold_star p)
      else
        TyBar (t, fold_star p)
    else
      t
  in
  match is_tyapp t with
  | Some (cons, args) ->
      begin match get_definition env cons with
      | Some (Concrete [branch]) ->
          let branch = instantiate_type branch args in
          wrap_if branch
      | Some (Abbrev t) ->
          let t = instantiate_type t args in
          wrap_if (expand_if_one_branch env t)
      | _ ->
        t
      end
  | None ->
      t
;;

let is_star env t =
  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in
  match t with
  | TyStar _ ->
      true
  | _ ->
      false
;;

let rec flatten_star env t =
  let t = modulo_flex env t in
  let t = expand_if_one_branch env t in
  match t with
  | TyStar (p, q) ->
      flatten_star env p @ flatten_star env q
  | TyEmpty ->
      []
  | TyAnchoredPermission (x, t) ->
      let t, ps = collect t in
      TyAnchoredPermission (x, t) :: ps
  | _ ->
      Log.check
        (get_kind_for_type env t = KPerm)
        "Bad internal usage of [flatten_star].";
      [t]
;;

(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  open MzPprint

  (* --------------------------------------------------------------------------- *)

  let print_var env v =
    let s = SurfaceSyntax.print_maybe_qualified Variable.print (Resugar.surface_print_var env v) in
    (* I have removed the color, it looks horrible in my terminal
       and produces garbage when output is redirected to a file. *)
    utf8string s
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

  let smallint i =
    let base = "₀" in
    let mkchar i =
      let str = String.copy base in
      str.[2] <- Char.chr (Char.code base.[2] + i);
      str
    in
    let rec mk acc i =
      if i > 0 then
        let digit = mkchar (i mod 10) in
        mk (digit :: acc) (i / 10)
      else
        List.rev acc
    in
    if i = 0 then
      string "0"
    else
      utf8string (String.concat "" (mk [] i))
  ;;


  let print_point env point =
    print_var env (get_name env point) ^^
    if Log.debug_level () > 0 then
      smallint (internal_uniqvarid env point)
    else
      empty
  ;;

  let pname buf (env, point) =
    pdoc buf ((fun () -> print_point env point), ())
  ;;

  let print_exports (env, mname) =
    let exports = List.map (fun x -> utf8string (Variable.print (fst3 x))) (get_exports env mname) in
    separate (string ", ") exports
  ;;

  let pexports buf env =
    pdoc buf (print_exports, env)
  ;;

  internal_pnames := pnames;;

  let print_binding env (x, k, _) =
    match k with
    | KType ->
        print_var env x
    | _ ->
        print_var env x ^^ string " : " ^^ print_kind k

  let rec print_quantified
      (env: env)
      (q: string)
      (name: name)
      (kind: kind)
      (typ: typ) =
    utf8string q ^^ lparen ^^ print_var env name ^^ space ^^ colon ^^ space ^^
    print_kind kind ^^ rparen ^^ dot ^^ jump (print_type env typ)

  and print_open env point =
    try
      if is_flexible env point then
        print_point env point ^^ star
      else if internal_wasflexible point then
        lparen ^^ string "inst→" ^^ print_type env (modulo_flex env (TyOpen point)) ^^ rparen
      else
        print_point env point
    with UnboundPoint | Assert_failure _ ->
      colors.red ^^ string "!! ☠ !!" ^^ colors.default


  (* TEMPORARY this does not respect precedence and won't insert parentheses at
   * all! *)
  and print_type env = function
    | TyUnknown ->
        string "unknown"

    | TyDynamic ->
        string "dynamic"

    | TyOpen point ->
        print_open env point

    | TyBound i ->
        string "TyBound(" ^^ int i ^^ string ")"

    | TyQ (q, _, _, _) as t ->
        let vars, env, t = strip_quantifiers_and_bind env q t in
       let delimiters =
         match q with
         | Forall -> brackets
         | Exists -> braces
       in
       prefix 0 1
         (delimiters (commas (print_binding env) vars))
         (print_type env t)

    | TyApp (head, args) ->
        application (print_type env) head (print_type env) args

    | TyTuple components ->
        tuple (print_type env) components

    | TyConcrete branch ->
        print_branch env branch

      (* Singleton types. *)
    | TySingleton typ ->
        equals ^^ print_type env typ

      (* Function types. *)
    | TyArrow (t1, t2) ->
        prefix 0 1
          (print_type env t1 ^^ space ^^ arrow)
          (print_type env t2)

      (* A special case: syntactic sugar for equations. *)
    | TyAnchoredPermission (ty1, TySingleton ty2) ->
        print_type env ty1 ^^ string " = " ^^ print_type env ty2

      (* Permissions. *)
    | TyAnchoredPermission (t1, t2) ->
        prefix 2 1
          (print_type env t1 ^^ space ^^ at)
          (print_type env t2)

    | TyEmpty ->
        string "empty"

    | TyStar (t1, t2) ->
        prefix 0 1
          (print_type env t1 ^^ space ^^ string "∗")
          (print_type env t2)

    | TyBar (p, q) ->
        parens (group (
         nest 2 (break 0 ^^ print_type env p) ^/^
         bar ^^ space ^^ nest 2 (print_type env q)
       ))

    | TyAnd (c, t) ->
        prefix 0 1
          (print_constraint env c ^^ space ^^ bar)
          (print_type env t)

  and print_constraint env (mode, t) =
    string (Mode.print mode) ^^ space ^^ print_type env t

  and print_data_field_def env (name, typ) =
      print_field_name name ^^ colon ^^ jump (print_type env typ)

  and print_branch env b =
    let fields = b.branch_fields in
    let clause = b.branch_adopts in
    let record =
      if List.length fields > 0 then
        space ^^ braces_with_nesting (
          separate_map semibreak (print_data_field_def env) fields
       )
      else
        empty
    in
    let clause =
      if equal env clause ty_bottom then
        empty
      else
        space ^^ string "adopts" ^^ space ^^ print_type env clause
    in
    string (DataTypeFlavor.print b.branch_flavor) ^^
    print_datacon (snd b.branch_datacon) ^^ record ^^ clause
  ;;

  let pfact buf fact =
    pdoc buf (Fact.internal_print, fact)
  ;;

  internal_pfact := pfact;;

  let print_facts (env: env): document =
    separate hardline (
      fold_definitions env (fun acc var _definition ->
        let name = get_name env var in
        let fact = get_fact env var in
        let kind = get_kind env var in
        (* let is_abstract = (fst definition = None) in *)
        (* I no longer print [is_abstract]. *)
        let env, params = make_datacon_letters env kind false in
        let param i : document =
          print_type env (TyOpen (List.nth params i))
        in
        let head =
          print_type env (TyApp (TyOpen var, List.map (fun v -> TyOpen v) params))
        in
        let printed_fact = string "Fact for" ^^ space ^^ print_var env name ^^
        colon ^^ jump (
          Fact.print param head fact
        ) in
        printed_fact :: acc
      ) []
    )
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

  let pconstraint buf (env, c) =
    pdoc buf ((fun () -> print_constraint env c), ())
  ;;

  let print_binders (env: env): document =
    utf8string "Γ (unordered) = " ^^
    separate
      (semi ^^ space)
      (map env (fun var -> separate_map (string " = ") (print_var env) (get_names env var)))
  ;;


end
