module Make (U : sig end) = struct
 
  (* Create a new instance of the hash-consing facility. *)

  let table =
    Hashcons.create()

  (* Names are represented as integers, but will be exported as
     an abstract type. *)

  type name =
      int

  (* Converting strings to names and back. *)

  let register (s : string) : name =
    Hashcons.add table s

  let print (n : name) : string =
    Hashcons.find table n

  (* Name equality. *)

  let equal (n1 : name) (n2 : name) =
    n1 = n2

  (* Maps over names. *)

  module Map = Patricia.Little

end

