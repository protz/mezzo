(** This module analyzes data type declaration to synthetize facts about the
   data types. *)

type bitmap = unit Types.LevelMap.t

type fact = Exclusive | Duplicable of bitmap | Affine

type facts = fact Types.LevelMap.t

val analyze_data_types: WellKindedness.data_type_env -> facts
val string_of_facts: WellKindedness.data_type_env -> facts -> string
