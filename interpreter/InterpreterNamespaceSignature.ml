(* A signature for a namespace. *)

(* The interpreter has several such namespaces (for variables, data constructors,
   etc.). *)

module type Namespace = sig

  (* A type of names. *)
  type name

  (* A global environment maps qualified and unqualified names to information. *)
  type 'a global_env

  (* An empty global environment. *)
  val empty: 'a global_env

  (* Looking up an unqualified name. *)
  val lookup_unqualified: name -> 'a global_env -> 'a

  (* Extending the environment with an unqualified name. *)
  val extend_unqualified: name -> 'a -> 'a global_env -> 'a global_env

  (* Looking up a qualified name. *)
  val lookup_qualified: Module.name -> name -> 'a global_env -> 'a

  (* Create a qualified version of an unqualified name. *)
  val qualify: Module.name -> name -> 'a global_env -> 'a global_env

  (* Create unqualified versions of the names that are qualified with [m]. *)
  val unqualify: Module.name -> 'a global_env -> 'a global_env

  (* Remove all unqualified names. *)
  val zap: 'a global_env -> 'a global_env

end
