module type MONAD = sig
  type 'a mon
  val (>>=): 'a mon -> ('a -> 'b mon) -> 'b mon
  val return: 'a -> 'a mon
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

module MOption: MONAD with type 'a mon = 'a option = struct
  type 'a mon = 'a option
  let (>>=) = Option.bind
  let (>>?=) = Option.bind
  let (|||) = Option.either
  let either = Option.either
  let fail = None
  let map = Option.map
  let iter = Option.iter
  let take = Hml_List.take
  let return x = Some x
  let dispatch = Hml_List.find_opt

  (* TODO share this accross monads *)
  let foldm f acc elts =
    List.fold_left (fun acc elt -> acc >>= fun acc -> f acc elt) acc elts
end
