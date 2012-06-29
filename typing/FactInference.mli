(** This module analyzes data type declaration to synthetize facts about the
   data types. *)

(** This function performs the elaboration phase where we build up more precise
 * facts about the various data types defined in the environment. *)
val analyze_data_types: Types.env -> Types.env

(** Get the fact for a type, which you can then pass to {Types.fact_leq}. *)
val analyze_type: Types.env -> Types.typ -> Types.fact

(** Is this type duplicable? *)
val is_duplicable: Types.env -> Types.typ -> bool

(** Is this type exclusive? *)
val is_exclusive: Types.env -> Types.typ -> bool
