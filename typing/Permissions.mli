(** This module provides permission manipulation functions. *)

open Types

(** [collect t] recursively walks down a type with kind TYPE, extracts all
    the permissions that appear into it (as tuple or record components), and
    returns the type without permissions as well as a list of types with kind
    PERM, which represents all the permissions that were just extracted. *)
val collect: typ -> typ * typ list

(** [unfold env t] returns [env, t] where [t] has been unfolded, which
    potentially led us into adding new points to [env]. The [hint] serves when
    making up names for intermediary variables. *)
val unfold: env -> ?hint:string -> typ -> env * typ

type refined_type = Both | One of typ

(** [refine_type env t1 t2] tries, given [t1], to turn it into something more
    precise using [t2]. It returns [Both] if both types are to be kept, or [One
    t3] if [t1] and [t2] can be combined into a more precise [t3].

    The order of the arguments does not matter: [refine_type env t1 t2] is equal
    to [refine_type env t2 t1]. *)
val refine_type: env -> typ -> typ -> env * refined_type

(** [refine env p t] adds [t] to the list of available permissions for [p],
    possibly by refining some of these permissions into more precise ones. *)
val refine: env -> point -> typ -> env

(** [unify env p1 p2] merges two points, and takes care of dealing with how the
    permissions should be merged. *)
val unify: env -> point -> point -> env

(** [add env point t] adds [t] to the list of permissions for [p], performing all
    the necessary legwork. *)
val add: env -> point -> typ -> env

(** [add_perm env t] adds a type [t] with kind PERM to [env], returning the new
    environment. *)
val add_perm: env -> typ -> env

(** [sub env point t] tries to extract [t] from the available permissions for
    [point] and returns, if successful, the resulting environment. *)
val sub: env -> point -> typ -> env option

(** [sub_perm env t] takes a type [t] with kind PERM, and tries to return the
    environment without the corresponding permission. *)
val sub_perm: env -> typ -> env option

(** [fold env point] tries to find (hopefully) one "main" type for [point], by
    folding back its "main" type [t] into a form that's suitable for one
    thing, and one thing only: printing. *)
val fold: env -> point -> typ option

val fold_type: env -> typ -> typ option

val full_merge: env -> point -> point -> env
