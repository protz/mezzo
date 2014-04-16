type name

type 'a dictionary = {
  map: (name -> name) -> 'a -> 'a
}

type 'a ty =
| TyOpaque : 'a dictionary -> 'a ty
| TyPair   : 'a ty * 'b ty -> ('a * 'b) ty

let rec map : type a . a ty -> (name -> name) -> a -> a =
  fun ty f x ->
    match ty with
    | TyOpaque { map } ->
        map f x
    | TyPair (ty1, ty2) ->
        let x1, x2 = x in
        map ty1 f x1, map ty2 f x2

type 'a tag =
| TagVar : name tag
| TagAbs : (name * term) tag
| TagApp : (term * term) tag

and term =
  Term   : 'a tag * 'a -> term

let ty_name : name ty =
  TyOpaque { map = fun f x -> f x }

let rec ty_term : term ty =
  TyOpaque { map = fun f x ->
    let Term (tag, arg) = x in
    Term (tag, map (describe tag) f arg)
  }

and describe : type a . a tag -> a ty =
  function
  | TagVar ->
      ty_name
  | TagAbs ->
      TyPair (ty_name, ty_term)
  | TagApp ->
      TyPair (ty_term, ty_term)

let map : (name -> name) -> term -> term =
  map ty_term

