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
end) : Namespace with type name = I.name = struct

  type name =
      I.name

  (* A local environment maps names to information. *)
  type 'a local_env =
      'a I.Map.t

  (* A global environment contains: *)
  type 'a global_env = {
    (* A map of module names to local environments. *)
    modules: 'a local_env Module.Map.t;
    (* A local environment for the current module. *)
    current: 'a local_env;
  }

  let lookup_local (x : I.name) (env : 'a local_env) : 'a =
    try
      I.Map.find x env
    with Not_found ->
      (* This name is undefined. *)
      assert false

  let extend_local (x : I.name) (a : 'a) (env : 'a local_env) : 'a local_env =
    I.Map.add x a env

  let lookup_unqualified (x : I.name) (env : 'a global_env) : 'a =
    lookup_local x env.current

  let extend_unqualified (x : I.name) (a : 'a) (env : 'a global_env) : 'a global_env =
    { env with current = extend_local x a env.current }

  let lookup_qualified (m : Module.name) (x : I.name) (env : 'a global_env) : 'a =
    lookup_local x (
      try
	Module.Map.find m env.modules
      with Not_found ->
	(* Unknown module. *)
	assert false
    )

  let qualify (m : Module.name) (env : 'a global_env) : 'a global_env =
    (* Check that this module is not already defined. *)
    assert (not (Module.Map.mem m env.modules));
    (* Define this module by adding a mapping of [m] to [env.current] to
       [env.modules]. Then, empty [env.current]. *)
    {
      modules = Module.Map.add m env.current env.modules;
      current = I.Map.empty;
    }

end

