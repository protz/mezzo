(** This module analyzes data type declaration to synthetize facts about the
   data types. *)

val analyze_data_types: Types.program_env -> Env.working_env -> Types.program_env
