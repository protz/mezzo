(* This is the translation of Mezzo to Untyped Mezzo. *)

val adopter_field: Variable.name
val translate_implementation: SurfaceSyntax.implementation -> UntypedMezzo.implementation
val translate_interface: SurfaceSyntax.interface -> UntypedMezzo.interface

