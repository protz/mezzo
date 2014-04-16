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
  | TyPair   : 'a ty * 'b ty -> ('a * 'b) ty
  | TyOpaque : 'a methods -> 'a ty

  module Stage2 (Y : sig

    val describe: ('a, 'kind) tag -> 'a ty

  end) = struct

    open Y

    let rec map : type a . a ty -> a -> a =
      fun ty x ->
      match ty with
      | TyUniv ->
          let Univ (tag, arg) = x in
          Univ (tag, map (describe tag) arg)
      | TyPair (ty1, ty2) ->
          let x1, x2 = x in
          map ty1 x1, map ty2 x2
      | TyOpaque { map } ->
          map x

  end

end

type name

type term (* a kind *)

module MyTag = struct

  type ('a, 'kind) tag =
  | TagVar : (name, term univ) tag
  | TagAbs : (name * term univ, term) tag
  | TagApp : (term univ * term univ, term) tag

  and 'kind univ =
    Univ : ('a, 'kind) tag * 'a -> 'kind univ

end

module S1 = Stage1(MyTag)

module MyDescribe = struct

  open MyTag
  open S1

  let ty_name : name ty =
    TyOpaque { map = fun x -> x }

  let ty_term : term univ ty =
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
  let map : term univ -> term univ = S2.map ty_term
end

type 'kind kind =
| KTerm : term kind

type ('a, 'kind) tag =
| TagVar : (name, term univ) tag
| TagAbs : (name * term univ, term) tag
| TagApp : (term univ * term univ, term) tag

and 'kind univ =
  Univ   : ('a, 'kind) tag * 'a -> 'kind univ

type 'a ty =
| TyName : name ty
| TyUniv : 'kind kind -> 'kind univ ty
| TyPair : 'a ty * 'b ty -> ('a * 'b) ty

let ty_term : term univ ty =
  TyUniv KTerm

let describe : type a kind . (a, kind) tag -> a ty =
  function
  | TagVar ->
      TyName
  | TagAbs ->
      TyPair (TyName, ty_term)
  | TagApp ->
      TyPair (ty_term, ty_term)

let rec map : type a . (name -> name) -> a ty -> a -> a =
  fun f ty x ->
    match ty with
    | TyName ->
        f x
    | TyUniv kind ->
        (* note: [kind] is unused *)
        let Univ (tag, arg) = x in
        Univ (tag, map f (describe tag) arg)
    | TyPair (ty1, ty2) ->
        let x1, x2 = x in
        map f ty1 x1, map f ty2 x2
