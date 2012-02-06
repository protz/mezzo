(* Variables form a space of identifiers. *)
include Identifier.Make(struct end)

(* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
let p buf var =
  Buffer.add_string buf (print var)
