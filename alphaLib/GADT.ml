type name

type 'a tag =
| TagVar : name tag
| TagAbs : (name * term) tag
| TagApp : (term * term) tag

and term =
  Term   : 'a tag * 'a -> term
  (* one would like to parameterize this def. over [tag] *)

type 'a ty =
| TyName : name ty
| TyTerm : term ty
    (* one would like to existentially abstract over [tag]
       provided [tag] comes with a [describe] function *)
| TyPair : 'a ty * 'b ty -> ('a * 'b) ty

let describe : type a . a tag -> a ty =
  function
  | TagVar ->
      TyName
  | TagAbs ->
      TyPair (TyName, TyTerm)
  | TagApp ->
      TyPair (TyTerm, TyTerm)

let rec map : type a . (name -> name) -> a ty -> a -> a =
  fun f ty x ->
    match ty with
    | TyName ->
        f x
    | TyTerm ->
        let Term (tag, arg) = x in
        Term (tag, map f (describe tag) arg)
    | TyPair (ty1, ty2) ->
        let x1, x2 = x in
        map f ty1 x1, map f ty2 x2

