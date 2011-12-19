(** This module analyzes data type declaration to synthetize facts about the
   data types. *)

type bitmap = unit Types.IndexMap.t

type fact = Exclusive | Duplicable of bitmap | Affine

type facts = fact Types.IndexMap.t

val analyze_data_types: Types.env -> facts
val string_of_facts: Types.env -> facts -> string
