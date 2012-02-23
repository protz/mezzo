type t = unit ref

let create () =
  ref ()

let equals =
  (==)
