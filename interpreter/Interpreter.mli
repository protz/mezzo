open SurfaceSyntax

(* The interpreter works with a program expressed in the surface syntax.
   The program may be composed of multiple units (a.k.a. modules). The
   interpreter expects the program to be well-typed, but does not assume
   that the abstract syntax tree has been annotated by the type-checker. *)

(* The type of interpreter environments. *)

type env

(* An empty environment. *)

val empty : env

(* Evaluating an interface/implementation pair returns an updated environment. *)

val eval_unit: env -> Module.name -> interface -> implementation -> env

(* Evaluating a lone implementation is permitted for convenience, but does not
   return an updated environment. *)

val eval_lone_implementation: env -> implementation -> unit

