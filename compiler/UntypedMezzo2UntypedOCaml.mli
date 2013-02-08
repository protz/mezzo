(* This is the translation of Untyped Mezzo to Untyped OCaml. *)

val translate_implementation: UntypedMezzo.implementation -> UntypedOCaml.implementation
val translate_interface: UntypedMezzo.interface -> UntypedOCaml.interface
val translate_interface_as_implementation_filter: UntypedMezzo.interface option -> UntypedOCaml.implementation

