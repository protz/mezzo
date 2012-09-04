module type MONAD = sig
  type 'a mon
  val (>>=): 'a mon -> ('a -> 'b mon) -> 'b mon
  val return: 'a -> 'a mon
end

module type NDMONAD = sig
  include MONAD

  val just: 'a mon -> 'a
  val either: 'a mon -> 'a mon -> 'a mon
  val trywith: 'a mon -> ('a -> 'b mon) -> 'b mon -> 'b mon
  val fail: 'a mon

  val map: ('a -> 'b) -> 'a mon -> 'b mon
  val iter: ('a -> unit) -> 'a mon -> unit

  val take: ('a -> 'b mon) -> 'a list -> ('a list * ('a * 'b)) mon
  val dispatch: ('a -> 'b mon) -> 'a list -> 'b mon

  (* Conversion from the option monad. *)
  val (>>?=): 'a option -> ('a -> 'b mon) -> 'b mon

  (* This is a precedence operator: take the first value, unless it's [fail],
   * and then take the second value. *)
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
  let trywith v f x = match v with None -> x | _ -> v >>= f
  let map = Option.map
  let iter = Option.iter
  let take = Hml_List.take
  let dispatch = Hml_List.find_opt
  let just = Option.extract

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
  let (|||) l1 l2 = match l1 with [] -> l2 | _ -> l1
  let either = (@)
  let fail = []
  let trywith v f x = match v with [] -> x | _ -> v >>= f
  let map = List.map
  let iter = List.iter
  let dispatch = Hml_List.map_flatten
  let take f l =
    let rec take sofar bss = function
      | hd :: tl ->
          let bs = f hd in
          let bs = List.map (fun b -> sofar @ tl, (hd, b)) bs in
          take (hd :: sofar) (bs :: bss) tl
      | [] ->
          bss
    in
    let bss = take [] [] l in
    List.flatten bss
  let just l = assert (List.length l = 1); List.hd l

  include Common(M)
end
