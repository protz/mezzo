type ('var, 'scope) ty =
| TyVar of 'var
| TyAtom
| TyArrow of ('var, 'scope) ty * ('var, 'scope) ty
| TyQ of 'scope

let rec map v s ty =
  match ty with
  | TyVar x ->
      let y = v x in
      if Obj.magic (==) x y then
        Obj.magic ty
      else
        TyVar y
  | TyAtom ->
      TyAtom
  | TyArrow (ty1, ty2) ->
      TyArrow (map v s ty1, map v s ty2)
  | TyQ b ->
      TyQ (s b)

type 'x var =
| External of 'x
| Internal of int

type 'x term =
  ('x var, 'x term) ty

type 'x substitution =
  'x RandomAccessList.t

(* [apply phi v] applies the substitution [phi]
   to the variable [v]. The result is always an external name. *)
let apply (phi : 'x substitution) (v : 'x var) : 'x =
  match v with
  | Internal i ->
      (* By assumption, the domain of [phi] includes [i], so we
         apply [phi] without fear. *)
      RandomAccessList.lookup i phi
  | External x ->
      (* An external name is unaffected. *)
      x

(* [apply_shift delta phi v] applies the substitution [phi], shifted up by [delta],
   to the variable [v]. The result is an external or internal name. *)
let apply_shift (delta : int) (phi : 'x substitution) (v : 'x var) : 'x var =
  match v with
  | Internal i when i >= delta ->
      (* By assumption, the domain of [phi] includes [i - delta], so we
         apply [phi] without fear. *)
      External (RandomAccessList.lookup (i - delta) phi)
  | _ ->
      (* An external name, or an internal name below [delta], is unaffected. *)
      v

type 'x abstraction =
| Suspension of 'x substitution * 'x term

let suspend phi ty =
  Suspension (phi, ty)

type 'x exposed =
  ('x, 'x abstraction) ty

(* Precondition: the domain of [phi] covers [ty]. *)
let subst phi ty =
  map (apply phi) (suspend phi) ty

let instantiate (susp : 'x abstraction) (x : 'x) : 'x exposed =
  let Suspension (phi, ty) = susp in
  subst (RandomAccessList.cons x phi) ty

let expose (ty : 'x term) : 'x exposed =
  subst RandomAccessList.empty ty

let rec push (delta : int) (phi : 'x substitution) (ty : 'x term) : 'x term =
  map
    (apply_shift delta phi)
    (push (delta + 1) phi)
    ty

let force (susp : 'x abstraction) : 'x term (* 1-closed *) =
  let Suspension (phi, ty) = susp in
  if RandomAccessList.is_empty phi then
    ty
  else
    push 1 phi ty

let close (ty : 'x exposed) : 'x term = (* 0-closed *)
  map
    (fun v -> External v)
    force
    ty

let replace (i : int) (x : 'x) : 'x var -> 'x var = function
  | External y when x == y -> (* TEMPORARY equality *)
      Internal i
  | v ->
      v

let rec abstract (i : int) (x : 'x) (ty : 'x term) : 'x term =
  map
    (replace i x)
    (abstract (i + 1) x)
    ty

let abstract x ty =
  Suspension (RandomAccessList.empty, abstract 0 x ty)

(* TEMPORARY songer à la construction en temps linéaire des types, dans
   le style de ce que fait KindCheck... Autres opérations? test d'égalité?
   fonctions de parcours diverses? etc. *)

