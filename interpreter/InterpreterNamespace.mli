(* Within each namespace, we handle the distinction between unqualified and
   qualified names as follows. A local environment maps unqualified names to
   information. A global environment maps module names to local environments,
   and also contains a local environment for the current module. *)

(* ---------------------------------------------------------------------------- *)

(* A signature for a namespace. *)

module type Namespace = sig

  (* A type of names. *)
  type name

  (* A global environment maps qualified and unqualified names to information. *)
  type 'a global_env

  (* Looking up an unqualified name. *)
  val lookup_unqualified: name -> 'a global_env -> 'a

  (* Extending the environment with a single unqualified name. *)
  val extend_unqualified: name -> 'a -> 'a global_env -> 'a global_env

  (* Looking up a qualified name. *)
  val lookup_qualified: Module.name -> name -> 'a global_env -> 'a

  (* Transforming all of the unqualified names bound so far into names
     qualified with the module name [m]. *)
  val qualify: Module.name -> 'a global_env -> 'a global_env

end

(* ---------------------------------------------------------------------------- *)

(* This functor creates a new namespace. *)

module MakeNamespace (I : sig
  (* See [parsing/Identifier]. *)
  type name
  module Map : GMap.S with type key = name
end) : Namespace with type name = I.name
