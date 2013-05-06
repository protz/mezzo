type name =
  int

module Map =
  Map.Make (struct
    type t = name
    let compare (x : name) (y : name) : int =
      Pervasives.compare x y
  end)

let fresh =
  let c = ref 0 in
  fun _ ->
    let x = !c in
    c := x + 1;
    x
  
