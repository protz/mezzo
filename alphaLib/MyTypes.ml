type ('x, 'p) expr =
| TyVar of 'x
| TyAtom
| TyArrow of ('x, 'p) expr * ('x, 'p) expr
| TyQ of 'p

open Obj

let rec subst fx fp ty =
  match ty with
  | TyVar x ->
      let ty' = fx x in
      begin match ty' with
      | TyVar x' when magic (==) x x' ->
	  magic ty
      | _ ->
	  ty'
      end
  | TyAtom ->
      TyAtom
  | TyArrow (ty1, ty2) ->
      let ty1' = subst fx fp ty1 in 
      let ty2' = subst fx fp ty2 in
      if magic (==) ty1 ty1' && magic (==) ty2 ty2' then
	magic ty
      else
	TyArrow (ty1', ty2')
  | TyQ p ->
      let p' = fp p in
      if magic (==) p p' then
	magic ty
      else
	TyQ p'

let var x =
  TyVar x

let rec fold fx fp ty accu =
  match ty with
  | TyVar x ->
      let accu = fx x accu in
      accu
  | TyAtom ->
      accu
  | TyArrow (ty1, ty2) ->
      let accu = fold fx fp ty1 accu in
      let accu = fold fx fp ty2 accu in
      accu
  | TyQ p ->
      let accu = fp p accu in
      accu

