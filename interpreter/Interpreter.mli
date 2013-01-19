open SurfaceSyntax

(* The type of interpreter environments. *)

type env

(* An empty environment. *)

val empty : env

(* Evaluating an interface/implementation pair returns an updated environment. *)

val eval_unit: env -> Module.name -> interface -> implementation -> env

(* Evaluating a lone implementation is permitted for convenience, but does not
   return an updated environment. *)

val eval_lone_implementation: env -> implementation -> unit

