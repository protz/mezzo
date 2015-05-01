open TypeCore

(** This function converts an internal name to a possibly-qualified name
    in the surface syntax. *)
val surface_print_name: env -> name -> Variable.name SurfaceSyntax.maybe_qualified

(** This function converts a type expressed in the internal syntax back
    to the surface syntax. *)
val resugar: env -> typ -> SurfaceSyntax.typ

