open Data

(* This module offers a representation of typing contexts -- which,
   roughly speaking, can be thought of as a conjunction of permissions
   and equations. *)

(* This representation is persistent: the operations below produce new
   contexts without destroying their arguments. *)

type context

(* A typing context is either inconsistent (which means that it represents a
   set of incompatible assumptions) or consistent. *)

val is_inconsistent: context -> bool

(* [unify x1 x2 context] adds the equation [x1 = x2] to the context [context].
   The term variables [x1] and [x2] must be in scope in [context]. *)

val unify: termvar -> termvar -> context -> context

(* [add x ty context] adds the permission [x: ty] to the context [context].
   The term variable [x] must be in scope in context, and the type [ty] 
   must be well-formed with respect to [context]. *)

val add: termvar -> typ -> context -> context

