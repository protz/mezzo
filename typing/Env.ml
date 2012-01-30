(* This module defines the « big » environment that we use for type-checking
 * a program. *)

open Types

module PUF = PersistentUnionFind

(** Currently, there's only one such environment per file. It's created after we
 * analyzed all type definitions, their well-kindedness, and inferred the facts
 * related to them. It is created once, and doesn't change afterwards. *)
type program_env = {
  type_for_datacon: level DataconMap.t;
  fact_for_type: FactInference.fact LevelMap.t;
  kind_for_type: SurfaceSyntax.kind LevelMap.t;
}

(** This is what is used by the various modules when type-checking a program. *)
type working_env = {
  (** Maps a program identifier to the correspond persistent union-find point.
   * This implictly represents the fact that we have equations between program
   * identifiers. The various maps and lists below thus refer to union-find
   * points, not program identifiers. *)
  point_of_ident: PUF.point LevelMap.t;

  (** The persistent version the union-find algorithm associates points with
   * permissions. *)
  state: permissions PUF.state;

  (** The current-working level. The AST has De Bruijn indices, but the
   * environment has levels. Crossing a binder when traversing the AST amounts
   * to incrementing the level in the environment. Mapping an index to a level
   * thus becomes [let the_level = env.level - index]. *)
  level: level;
}

(** We separate duplicable permissions and exclusive permissions *)
and permissions = {
  duplicable: typ list;
  exclusive: typ list;
}

let create
    (data_type_env: WellKindedness.data_type_env)
    (facts: FactInference.facts): program_env =
  let kind_for_type =
    LevelMap.map
      (fun (_flag, _name, kind, _def) -> kind)
      data_type_env.WellKindedness.data_type_map
  in
  let fact_for_type = facts in
  let type_for_datacon =
    let map = DataconMap.empty in
    LevelMap.fold
      (fun level (_flag, _name, _kind, branches) map ->
        List.fold_left (fun map (name, _fields) ->
          DataconMap.add name level map) map branches)
      data_type_env.WellKindedness.data_type_map map
  in
  { kind_for_type; fact_for_type; type_for_datacon }
