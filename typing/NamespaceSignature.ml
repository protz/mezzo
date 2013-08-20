(** A signature for a namespace. *)

(** The interpreter has several such namespaces (for variables, data constructors,
   etc.). *)

module type Namespace = sig

  (** A type of names. *)
  type name

  (** A global environment maps qualified and unqualified names to information. *)
  type 'a global_env

  (** An empty global environment. *)
  val empty: 'a global_env

  (** Looking up an unqualified name. May raise [Not_found]. *)
  val lookup_unqualified: name -> 'a global_env -> 'a

  (** Extending the environment with an unqualified name. *)
  val extend_unqualified: name -> 'a -> 'a global_env -> 'a global_env

  (** Clear unqualified names from the environment. *)
  val clear_unqualified: 'a global_env -> 'a global_env

  (** Looking up a qualified name. May raise [Not_found]. *)
  val lookup_qualified: Module.name -> name -> 'a global_env -> 'a

  (** Extending the environment with a qualified name. *)
  val extend_qualified: Module.name -> name -> 'a -> 'a global_env -> 'a global_env

  (** Looking up a possibly qualified name. May raise [Not_found]. *)
  val lookup_maybe_qualified: name SurfaceSyntax.maybe_qualified -> 'a global_env -> 'a

  (** Create a qualified version of an unqualified name. *)
  val qualify: Module.name -> name -> 'a global_env -> 'a global_env

  (** Mark that the module [m] exists and will no longer be modified. *)
  val freeze: Module.name -> 'a global_env -> 'a global_env

  (** Create unqualified versions of the names that are qualified with [m]. *)
  val unqualify: Module.name -> 'a global_env -> 'a global_env

  (** Remove all unqualified names. *)
  val zap: 'a global_env -> 'a global_env

  open PPrint

  (** Pretty-printing an environment. *)
  val print_global_env: ('a -> document) -> 'a global_env -> document

end

