open NamespaceSignature

(* This functor creates a new namespace. *)

module MakeNamespace (I : sig
  (* See [parsing/Identifier]. *)
  type name
  val print: name -> string
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
    I.Map.find x env

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
        Log.error "Internal failure: unknown module: %s (while looking up %s::%s)" (Module.print m) (Module.print m) (I.print x)
    )

  let lookup_maybe_qualified (x : name SurfaceSyntax.maybe_qualified) (env : 'a global_env) : 'a =
    match x with
    | SurfaceSyntax.Unqualified x ->
        lookup_unqualified x env
    | SurfaceSyntax.Qualified (m, x) ->
        lookup_qualified m x env

  let freeze (m : Module.name) (env : 'a global_env) : 'a global_env =
    (* If necessary, create an empty set of bindings for this module.
       We do this so that if a module happens to export no values, or
       no data constructors, there will still be an entry for it. This
       helps when debugging. *)
    if Module.Map.mem m env.modules then
      env
    else
      { env with modules = Module.Map.add m I.Map.empty env.modules }

  (* When used directly, this function may seem fishy, because we should
     never need to add a single definition to an existing module. It is
     used by [qualify] below. It is not used directly by the interpreter,
     but is used by [KindCheck]. *)
  let extend_qualified (m : Module.name) (x : name) (a : 'a) (env : 'a global_env) : 'a global_env =
    (* Look up the bindings for the module [m]. *)
    let menv =
      try
        Module.Map.find m env.modules
      with Not_found ->
        (* If necessary, create an empty set of bindings for this module. *)
        I.Map.empty
    in
    (* Check that [m::x] is not defined already. *)
    Log.check (not (I.Map.mem x menv))
      "extend_qualified: %s::%s is already defined." (Module.print m) (I.print x);
    (* Add a binding for [m::x]. *)
    { env with modules = Module.Map.add m (I.Map.add x a menv) env.modules }

  let qualify (m : Module.name) (x : name) (env : 'a global_env) : 'a global_env =
    (* Look up the unqualified name [x]. *)
    let a =
      try
        lookup_unqualified x env
      with Not_found ->
        (* This name is undefined. *)
        Log.error "Internal failure: undefined variable or data constructor: %s" (I.print x)
    in
    (* Add a binding to the same value for [m::x]. *)
    extend_qualified m x a env

  let unqualify (m : Module.name) (env : 'a global_env) : 'a global_env =
    (* Check that this module is already defined. *)
    let menv : 'a local_env =
      try
        Module.Map.find m env.modules
      with Not_found ->
        (* Undefined module. Thanks to our use of [freeze] above, this is
          an error. *)
        Log.error "Internal failure: unknown module: %s (while evaluating \"open %s\")" (Module.print m) (Module.print m)
    in
    (* For every name of the form [m::x], create a new local name of the
       form [x]. The name [m::x] remains defined, of course. *)
    { env with current = I.Map.union env.current menv }

  let zap (env : 'a global_env) : 'a global_env =
    { env with current = I.Map.empty }

  (* Pretty-printers; for debugging. *)

  open MzPprint

  let print_local_env (f : 'a -> document) (env : 'a local_env) : document =
    I.Map.fold (fun x a accu ->
      accu ^^ (
        ((string (I.print x) ^^ colon) ^//^ f a) ^^ hardline
      )
    ) env empty

  let print_module_env (f : 'a -> document) (env : 'a Module.Map.t) : document =
    Module.Map.fold (fun x a accu ->
      accu ^^ (
        ((string (Module.print x) ^^ colon) ^//^ f a) ^^ hardline
      )
    ) env empty

  let print_global_env (f : 'a -> document) (env : 'a global_env) : document =
    print_module_env (print_local_env f) (
      (* Add the current environment as a pseudo-module. *)
      Module.Map.add (Module.register "<current>") env.current env.modules
    )

end

