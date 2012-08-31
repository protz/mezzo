(** This module provides permission manipulation functions. *)

module Make: functor (M: Monadic.NDMONAD) -> sig

  open M

  open Types

  (** [collect t] recursively walks down a type with kind TYPE, extracts all
      the permissions that appear into it (as tuple or record components), and
      returns the type without permissions as well as a list of types with kind
      PERM, which represents all the permissions that were just extracted. *)
  val collect: typ -> typ * typ list

  (** [unfold env t] returns [env, t] where [t] has been unfolded, which
      potentially led us into adding new points to [env]. The [hint] serves when
      making up names for intermediary variables. *)
  val unfold: env -> ?hint:name -> typ -> (env * typ) mon

  (** [unify env p1 p2] merges two points, and takes care of dealing with how the
      permissions should be merged. *)
  val unify: env -> point -> point -> env mon

  (** [add env point t] adds [t] to the list of permissions for [p], performing all
      the necessary legwork. *)
  val add: env -> point -> typ -> env mon

  (** [add_perm env t] adds a type [t] with kind PERM to [env], returning the new
      environment. *)
  val add_perm: env -> typ -> env mon

  (** [sub env point t] tries to extract [t] from the available permissions for
      [point] and returns, if successful, the resulting environment. *)
  val sub: env -> point -> typ -> env mon

  (** [sub_perm env t] takes a type [t] with kind PERM, and tries to return the
      environment without the corresponding permission. *)
  val sub_perm: env -> typ -> env mon

  (** [sub_type env t1 t2] tries to perform [t1 - t2]. It is up to the caller to
      "do the right thing" by not discarding [t1] if it was not duplicable.
      Unifications may be performed, hence the return environment. *)
  val sub_type: env -> typ -> typ -> env mon

  (** [fold env point] tries to find (hopefully) one "main" type for [point], by
      folding back its "main" type [t] into a form that's suitable for one
      thing, and one thing only: printing. *)
  val fold: env -> point -> typ option

  val fold_type: env -> typ -> typ option

  val add_hint: (name option) -> string -> (name option)

  (** Returns all the duplicable permissions for a given point [p], except [=p]
     itself. *)
  val dup_perms_no_singleton: env -> point -> typ list

  (** This is for debugging, it runs a consistency check on a given environment. *)
  val safety_check: env -> unit

  (* Strip out all the constraints from a type. *)
  val collect_constraints: typ -> typ * duplicity_constraint list

  val add_constraints: env -> duplicity_constraint list -> env

end
