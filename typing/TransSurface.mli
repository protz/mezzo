open SurfaceSyntax
open KindCheckGlue

(** Translating the surface syntax down into the core language syntax. *)

(** [translate_type_reset] translates a type. *)
val translate_type_reset: env -> typ -> TypeCore.typ

(** [translate_data_type_group extend env group] translates a data type group.
    The [extend] function is passed a (list of) pairs of a data type name and
    a kind, and must extend the environment in a suitable way (i.e., this name
    could be mapped to a fresh variable, or to an existing point; see
    [KindCheck]). The function returns a pair of an environment that has been
    extended with new types and new data constructors, and a translated data
    type group. *)
val translate_data_type_group:
  (env -> type_binding list -> env) ->
  env ->
  data_type_group ->
  env * TypeCore.data_type_group

(** [translate_implementation] translates a compilation unit. *)
val translate_implementation: env -> toplevel_item list -> Expressions.implementation

(** [translate_interface] translates an interface. *)
val translate_interface: env -> toplevel_item list -> Expressions.interface
