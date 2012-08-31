module type MONAD = sig
  type 'a mon
  val (>>=): 'a mon -> ('a -> 'b mon) -> 'b mon
  val return: 'a -> 'a mon
end

module type NDMONAD = sig
  include MONAD

  val either: 'a mon -> 'a mon -> 'a mon
  val fail: 'a mon

  val map: ('a -> 'b) -> 'a mon -> 'b mon
  val iter: ('a -> unit) -> 'a mon -> unit

  val take: ('a -> 'b mon) -> 'a list -> ('a list * ('a * 'b)) mon
  val dispatch: ('a -> 'b mon) -> 'a list -> 'b mon

  (* Conversion from the option monad. *)
  val (>>?=): 'a option -> ('a -> 'b mon) -> 'b mon

  (* Same as [either]. *)
  val (|||): 'a mon -> 'a mon -> 'a mon

  (* Generic operations *)
  val foldm: ('a -> 'b -> 'a mon) -> 'a mon -> 'b list -> 'a mon
end

module Common (M: MONAD) = struct
  open M

  let foldm f acc elts =
    List.fold_left (fun acc elt -> acc >>= fun acc -> f acc elt) acc elts
end

module MOption: NDMONAD with type 'a mon = 'a option = struct
  module M: MONAD with type 'a mon = 'a option = struct
    type 'a mon = 'a option
    let (>>=) = Option.bind
    let return x = Some x
  end

  include M

  let (>>?=) = Option.bind
  let (|||) = Option.either
  let either = Option.either
  let fail = None
  let map = Option.map
  let iter = Option.iter
  let take = Hml_List.take
  let dispatch = Hml_List.find_opt

  include Common(M)
end

module MList: NDMONAD with type 'a mon = 'a list = struct
  module M: MONAD with type 'a mon = 'a list = struct
    type 'a mon = 'a list
    let (>>=) l f = Hml_List.map_flatten f l
    let return x = [x]
  end

  include M

  let (>>?=) = function Some x -> fun f -> f x | None -> fun _ -> []
  let (|||) = (@)
  let either = (@)
  let fail = []
  let map = List.map
  let iter = List.iter
  let dispatch = Hml_List.map_flatten
  let take = assert false

  include Common(M)
end
