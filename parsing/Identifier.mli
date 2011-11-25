(* This functor creates a fresh abstract type of names.
   It is typically invoked once for each namespace. *)

module Make (U : sig end) : sig

  (* An abstract type of names. *)

  type name

  (* Names stand for strings: names and string are inter-convertible. *)

  val register: string -> name
  val print: name -> string

  (* Names can be efficiently compared. *)

  val equal: name -> name -> bool

  (* We have efficient maps over names. *)

  module Map : GMap.S with type key = name

end

