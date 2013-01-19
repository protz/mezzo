open InterpreterNamespaceSignature

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

  let empty : 'a global_env = {
    modules = Module.Map.empty;
    current = I.Map.empty;
  }

  let lookup_local (x : name) (env : 'a local_env) : 'a =
    try
      I.Map.find x env
    with Not_found ->
      (* This name is undefined. *)
      assert false

  let extend_local (x : name) (a : 'a) (env : 'a local_env) : 'a local_env =
    I.Map.add x a env

  let lookup_unqualified (x : name) (env : 'a global_env) : 'a =
    lookup_local x env.current

  let extend_unqualified (x : name) (a : 'a) (env : 'a global_env) : 'a global_env =
    { env with current = extend_local x a env.current }

  let lookup_qualified (m : Module.name) (x : name) (env : 'a global_env) : 'a =
    lookup_local x (
      try
	Module.Map.find m env.modules
      with Not_found ->
	(* Unknown module. *)
	assert false
    )

  let qualify (m : Module.name) (x : name) (env : 'a global_env) : 'a global_env =
    (* Look up the unqualified name [x]. *)
    let a = lookup_unqualified x env in
    (* Look up the bindings for the module [m]. *)
    let menv =
      try
	Module.Map.find m env.modules
      with Not_found ->
	(* If necessary, create an empty set of bindings for this module. *)
	I.Map.empty
    in
    (* Check that [m::x] is not defined already. *)
    assert (not (I.Map.mem x menv));
    (* Add a binding for [m::x]. *)
    { env with modules = Module.Map.add m (I.Map.add x a menv) env.modules }

  let unqualify (m : Module.name) (env : 'a global_env) : 'a global_env =
    (* Check that this module is already defined. *)
    let menv : 'a local_env =
      try
	Module.Map.find m env.modules
      with Not_found ->
	(* Undefined module. *)
	assert false
    in
    (* For every name of the form [m::x], create a new local name of the
       form [x]. The name [m::x] remains defined, of course. *)
    { env with current = I.Map.union env.current menv }

  let zap (env : 'a global_env) : 'a global_env =
    { env with current = I.Map.empty }

end

