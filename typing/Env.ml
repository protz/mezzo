(* This module defines the « big » environments that we use for type-checking
 * a program. *)

open Types

(** Currently, there's only one such environment per file. It's created after we
 * analyzed all type definitions, their well-kindedness, and inferred the facts
 * related to them. It is created once, and doesn't change afterwards.
 * Everything in there has levels as keys. *)
type program_env = {
  type_for_datacon: level DataconMap.t;
  fact_for_type: FactInference.fact LevelMap.t;
  def_for_type: WellKindedness.data_type_entry LevelMap.t;
}

(** This is what is used by the various modules when type-checking a program.
 * Everything in there is levels too, and we're storing the current levels (both
 * for types and expressions). *)
type working_env = {
  (** Maps a program identifier to the correspond persistent union-find point.
   * This implictly represents the fact that we have equations between program
   * identifiers. The various maps and lists below thus refer to union-find
   * points, not program identifiers. *)
  point_of_ident: PersistentUnionFind.point LevelMap.t;

  (** The persistent version the union-find algorithm associates points with
   * permissions. *)
  state: permissions PersistentUnionFind.state;

  (** The current-working level. The AST has De Bruijn indices, but the
   * environment has levels. Crossing a binder when traversing the AST amounts
   * to incrementing the level in the environment. Mapping an index to a level
   * thus becomes [let the_level = env.level - index]. *)
  elevel: level;

  (** The state of flexible variables. We introduce flexible variables to
   * perform some sort of limited, local type inference. Flexible variables can
   * be unified together, and unified with a “real” type.
   *)
  flexible_state: descriptor PersistentUnionFind.state;

  (** A mapping from De Bruijn levels, to names suitable for printing. For
   * binders in expressions. *)
  name_for_expr: string LevelMap.t;

  (** The current level for types. *)
  tlevel: level;

  (** A mapping from De Bruijn levels, to names suitable for printing. Use it
   * to build a [TypePrinter.print_env]. *)
  name_for_type: string LevelMap.t;
}

(** We separate duplicable permissions and exclusive permissions *)
and permissions = {
  duplicable: typ list;
  exclusive: typ list;
}

and descriptor = {
  structure: typ option; (* No mutable keyword here, since we're using a functional union-find. *)
}


let create
    (data_type_env: WellKindedness.data_type_env)
    (facts: FactInference.facts): program_env * working_env =
  let fact_for_type = facts in
  let type_for_datacon = data_type_env.WellKindedness.cons_map in
  let def_for_type = data_type_env.WellKindedness.data_type_map in
  let program_env = {
    fact_for_type;
    type_for_datacon;
    def_for_type
  } in
  let print_env =
    WellKindedness.KindPrinter.create_and_populate_print_env program_env.def_for_type
  in
  let working_env = {
    point_of_ident = LevelMap.empty;
    state = PersistentUnionFind.init ();
    flexible_state = PersistentUnionFind.init ();
    elevel = 0;
    name_for_expr = LevelMap.empty;
    tlevel = print_env.TypePrinter.level;
    name_for_type = print_env.TypePrinter.names;
  } in
  program_env, working_env
;;

let name_for_expr (working_env: working_env) (level: level): string =
  let open WellKindedness in
  match LevelMap.find_opt level working_env.name_for_expr with
  | Some name ->
      name
  | None ->
      Log.error "There is no expr defined at level %d" level
;;

let name_for_type (working_env: working_env) (level: level): string =
  let open WellKindedness in
  match LevelMap.find_opt level working_env.name_for_type with
  | Some name ->
      name
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let branches_for_type (program_env: program_env) (level: level): data_type_def_branch list =
  let open WellKindedness in
  match LevelMap.find_opt level program_env.def_for_type with
  | Some (Concrete (_, _name, _kind, branches)) ->
      branches 
  | Some (Abstract (name, _)) ->
      Log.error "No branches for type %a, it is abstract" Variable.p name
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let fact_for_type (program_env: program_env) (level: level): FactInference.fact =
  let open WellKindedness in
  match LevelMap.find_opt level program_env.fact_for_type with
  | Some fact ->
      fact
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let kind_for_type (program_env: program_env) (level: level): kind =
  let open WellKindedness in
  match LevelMap.find_opt level program_env.def_for_type with
  | Some (Concrete (_, _name, kind, _) | Abstract (_name, kind)) ->
      kind
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let type_for_datacon (program_env: program_env) (datacon: Datacon.name): level =
  let open WellKindedness in
  match DataconMap.find_opt datacon program_env.type_for_datacon with
  | Some level ->
      level
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let permissions_for_ident (working_env: working_env) (level: level): permissions =
  let point = LevelMap.find level working_env.point_of_ident in
  PersistentUnionFind.find point working_env.state

module EnvPrinter = struct

  open Hml_Pprint

  let make_tprint_env (working_env: working_env): TypePrinter.print_env =
    let open TypePrinter in
    { level = working_env.tlevel; names = working_env.name_for_type }
  ;;

  let print_type (working_env, t: working_env * typ): document =
    TypePrinter.print_type (make_tprint_env working_env) t
  ;;

  let print_permissions (working_env, level: working_env * level): document =
    let tprint_env = make_tprint_env working_env in
    let { duplicable; exclusive } = permissions_for_ident working_env level in
    let duplicable = List.map (TypePrinter.print_type tprint_env) duplicable in
    let exclusive = List.map (TypePrinter.print_type tprint_env) exclusive in
    let exclusive = List.map
      (fun doc -> colors.underline ^^ doc ^^ colors.default) exclusive
    in
    join (comma ^^ break1) (duplicable @ exclusive)
  ;;

  let print_working_env (working_env: working_env): document =
    let header =
      let str = "PERMISSIONS:" in
      let line = String.make (String.length str) '-' in
      (string str) ^^ hardline ^^ (string line)
    in
    let lines = Hml_List.make working_env.elevel (fun level ->
      let name = name_for_expr working_env level in
      let perms = print_permissions (working_env, level) in
      (string name) ^^ colon ^^ space ^^ (nest 2 perms)
    ) in
    let lines = join break1 lines in
    header ^^ (nest 2 (break1 ^^ lines))

  let pdoc (buf: Buffer.t) (f, env: ('env -> document) * 'env): unit =
    PpBuffer.pretty 1.0 Bash.twidth buf (f env)

end
