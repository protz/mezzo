open NamespaceSignature

(* This functor creates a new namespace. *)

module MakeNamespace (I : sig
  (* See [parsing/Identifier]. *)
  type name
  val print: name -> string
  module Map : GMap.S with type key = name
end) : Namespace with type name = I.name

