(* Data constructors form a space of identifiers. *)
include Identifier.Make(struct end)

(* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
let p buf con =
  Buffer.add_string buf (print con)
