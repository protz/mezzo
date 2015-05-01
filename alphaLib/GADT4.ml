module Stage1 (X : sig

  type ('a, 'kind) tag

  type 'kind univ =
    Univ : ('a, 'kind) tag * 'a -> 'kind univ

end) = struct

  open X

  type 'a methods = {
    map: 'a -> 'a
  }

  type 'a ty =
  | TyUniv   : 'kind univ ty
  | TyUnit   : unit ty
  | TyPair   : 'a ty * 'b ty -> ('a * 'b) ty
  | TyOpaque : 'a methods -> 'a ty

  module Stage2 (Y : sig

    val describe: ('a, 'kind) tag -> 'a ty

  end) = struct

    open Y

    let rec map : type a . a ty -> a -> a =
      fun ty x ->
      match ty, x with
      | TyUniv,
        Univ (tag, arg) ->
          let arg' = map (describe tag) arg in
          if arg == arg' then
            x
          else
            Univ (tag, arg')
      | TyUnit,
        () ->
          ()
      | TyPair (ty1, ty2),
        (x1, x2) ->
          let x1' = map ty1 x1
          and x2' = map ty2 x2 in
          if x1 == x1' && x2 == x2' then
            x
          else
            (x1', x2')
      | TyOpaque { map },
        x ->
          map x

  end

end

type 'name term (* a kind *)

module MyTag = struct

  type ('a, 'kind) tag =
  | TagVar : ('name, 'name term) tag
  | TagAbs : ('name * 'name term univ, 'name term) tag
  | TagApp : ('name term univ * 'name term univ, 'name term) tag

  and 'kind univ =
    Univ : ('a, 'kind) tag * 'a -> 'kind univ

end

module S1 = Stage1(MyTag)

module MyDescribe = struct

  open MyTag
  open S1

  let ty_name : 'name ty =
    TyOpaque { map = fun x -> x }

  let ty_term : 'name term univ ty =
    TyUniv

  let describe : type a kind . (a, kind) tag -> a ty =
    function
    | TagVar ->
        ty_name
    | TagAbs ->
        TyPair (ty_name, ty_term)
    | TagApp ->
        TyPair (ty_term, ty_term)

end

module S2 = S1.Stage2(MyDescribe)

module Test = struct

  open MyTag
  open MyDescribe

  let map : 'name term univ -> 'name term univ = fun t -> S2.map ty_term t

  let t : int term univ =
    Univ (TagVar, 0)

  let u : int term univ =
    map t

  let t : string term univ =
    Univ (TagVar, "x")

  let u : string term univ =
    map t

  let test (t : int term univ) : int term univ =
    match t with
    | Univ (TagApp, (
        Univ (TagAbs, (x, t)),
        u
      )) ->
        u
    | u ->
        u

end

