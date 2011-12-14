(** This module analyzes data type declaration to synthetize facts about the
   data types. *)

(** The {!TyCon} module builds upon the previously defined {!Types} and
   {!Variable} modules. *)
module TyCon: ModeDeduction.TYCON

module MD: module type of ModeDeduction.Make(Mode)(TyCon)

type facts = MD.rule list

val analyze_data_types: Types.env -> facts
val string_of_facts: facts -> string
