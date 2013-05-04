(* A variable is either external (a name) or internal (a de Bruijn index). *)

type 'x var =
| External of 'x
| Internal of int

(* A renaming is a mapping of internal names to external names. This sort
   of renaming is used when opening an abstraction (i.e., unbinding). *)

type 'x renaming =
    'x RandomAccessList.t

(* [apply rho v] applies the renaming [rho] to the variable [v]. The result
   is an external name. We assume that the variable [v] is either external
   or in the domain of [rho]. *)

let apply (rho : 'x renaming) (v : 'x var) : 'x =
  match v with
  | Internal i ->
      (* By assumption, the domain of [rho] includes [i], so we apply [rho]
	 without fear. *)
      RandomAccessList.lookup i rho
  | External x ->
      (* An external name is unaffected. *)
      x

(* [apply_shift delta rho v] applies the renaming [rho], shifted up by [delta],
   to the variable [v]. The result is an external or internal name. We assume
   that the variable [v] is either external or in the domain of [delta/rho]. *)

let apply_shift (delta : int) (rho : 'x renaming) (v : 'x var) : 'x var =
  match v with
  | Internal i when i >= delta ->
      (* By assumption, the domain of [rho] includes [i - delta], so we apply
	 [rho] without fear. *)
      External (RandomAccessList.lookup (i - delta) rho)
  | _ ->
      (* An external name, or an internal name below [delta], is unaffected. *)
      v

(* [replace i x] is the function of variables to variables that replaces
   the external name [x] with the internal index [i]. *)

let replace (i : int) (x : 'x) : 'x var -> 'x var = function
  | External y when x == y -> (* TEMPORARY parameterize with equality on 'x *)
      Internal i
  | v ->
      v

type ('x, 'e) suspension =
    Suspension of 'x renaming * 'e

let suspend rho e =
  Suspension (rho, e)

open Signatures

module Make (E : EXPRESSION) = struct

  (* The standard locally nameless representation is obtained by filling
     variable holes with ['x var] and by filling expression holes
     (recursively) with ['x expr]. *)

  (* TEMPORARY a type abbreviation should be permitted? (with -rectypes) *)
  type 'x expr =
      E of ('x var, 'x expr) E.expr

  (* [unbind delta rho e] requires [delta/rho/e] to be 0-closed. Its effect
     is to apply [delta/rho] to [e]. *)

  let rec unbind (delta : int) (rho : 'x renaming) ((E e) : 'x expr) : 'x expr =
    E (
      E.map
	(apply_shift delta rho)
	(unbind (delta + 1) rho)
	e
    )

  (* [bind i x e] replaces the external name [x] with the internal index [i]
     throughout the expression [e]. *)

  let rec bind (i : int) (x : 'x) ((E e) : 'x expr) : 'x expr =
    E (
      E.map
	(replace i x)
	(bind (i + 1) x)
	e
    )

  (* An abstraction is the suspended application of a renaming to an
     expression in the standard representation. In the following,
     every abstraction is 1-closed. *)

  type 'x abstraction =
      ('x, 'x expr) suspension

  (* The exposed (or transparent) representation prescribes the presence
     of an abstraction at each binding site in the first layer. *)

  type 'x exposed =
    ('x, 'x abstraction) E.expr

  (* [subst rho e] requires that the domain of [rho] include [e], or in
     other words, that [rho/e] be 0-closed. Its effect is to apply [rho]
     to [e], stopping at the first layer of binders, hence producing an
     exposed expression. *)

  let subst (rho : 'x renaming) ((E e) : 'x expr) : 'x exposed =
    E.map (apply rho) (suspend rho) e

  let instantiate (a : 'x abstraction) (x : 'x) : 'x exposed =
    let Suspension (rho, e) = a in
    subst (RandomAccessList.cons x rho) e

  let expose (e : 'x expr) : 'x exposed =
    subst RandomAccessList.empty e

  let force (a : 'x abstraction) : 'x expr =
    let Suspension (rho, e) = a in
    (* The abstraction [a] is 1-closed, so the domain of [1/rho] covers [e].
       If [rho] happens to be the identity, then [1/rho] is the identity as
       well, and we can just return [e]. (This optimization allows us to
       encode a trivial abstraction as one that contains an identity
       renaming.)  Otherwise, we apply [1/rho] to [e]. *)
    if RandomAccessList.is_empty rho then
      e
    else
      unbind 1 rho e

  let close (e : 'x exposed) : 'x expr = (* 0-closed *)
    E (
      E.map
	(fun v -> External v)
	force
	e
    )

  (* If [e] is 0-closed, then [bind 0 x e] is 1-closed.
     We wrap it as a (trivial) abstraction. *)

  let bind x e =
    Suspension (RandomAccessList.empty, bind 0 x e)

end

