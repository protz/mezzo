type name =
  int

type t =
  name

let compare (x : name) (y : name) : int =
  Pervasives.compare x y

let fresh =
  let c = ref 0 in
  fun _ ->
    let x = !c in
    c := x + 1;
    x
  
