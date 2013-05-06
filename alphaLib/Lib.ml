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

  let map (fx : 'x1 -> 'x2) (fp : 'p1 -> 'p2) (e : ('x1, 'p1) E.expr) : ('x2, 'p2) E.expr =
    E.subst
      (fun x -> E.var (fx x))
      fp
      e

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
      map
	(apply_shift delta rho)
	(unbind (delta + 1) rho)
	e
    )

  (* [bind i x e] replaces the external name [x] with the internal index [i]
     throughout the expression [e]. *)

  let rec bind (i : int) (x : 'x) ((E e) : 'x expr) : 'x expr =
    E (
      map
	(replace i x)
	(bind (i + 1) x)
	e
    )

  (* [subst phi e] applies the substitution [phi], which maps external
     names to 0-closed expressions, to the expression [e]. *)

  let rec subst (phi : 'x -> 'x expr) ((E e) : 'x expr) : 'x expr =
    E (
      E.subst
	(function
	  | External x -> (match phi x with E e -> e)
	  | Internal _ as v -> E.var v)
	(subst phi)
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

  (* [attack rho e] requires that the domain of [rho] include [e], or in
     other words, that [rho/e] be 0-closed. Its effect is to apply [rho]
     to [e], stopping at the first layer of binders, hence producing an
     exposed expression. *)

  let attack (rho : 'x renaming) ((E e) : 'x expr) : 'x exposed =
    map (apply rho) (suspend rho) e

  let instantiate (a : 'x abstraction) (x : 'x) : 'x exposed =
    let Suspension (rho, e) = a in
    attack (RandomAccessList.cons x rho) e

  let expose (e : 'x expr) : 'x exposed =
    attack RandomAccessList.empty e

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
      map
	(fun v -> External v)
	force
	e
    )

  (* If [e] is 0-closed, then [bind 0 x e] is 1-closed.
     We wrap it as a (trivial) abstraction. *)

  let bind x e =
    Suspension (RandomAccessList.empty, bind 0 x e)

end

module MakeWithPattern (N : NAME) (P : PATTERN) (E : EXPRESSION) = struct

  module NameMap =
    Map.Make(N)

  (* The locally nameless representation of expressions is obtained by filling
     variable holes with [N.name var] and by filling pattern holes with
     [closed_pat]. In closed patterns, we fill variable holes with [int] and
     fill inner and outer expression holes with [expr]. *)

  (* In the definition of [closed_pat], we could choose to fill variable holes
     with [unit]. This would yield a representation where bound names are
     anonymous. The present decision allows representing non-linear patterns,
     i.e., patterns where a name occurs several times. We adopt the convention
     that, once an abstraction has been closed, the names that occur in the
     pattern form an interval of the form [0, n), for some value of [n], which
     is less than or equal to the number of variable holes in the pattern.
     We refer to [n] as the gap. *)

  (* A technical remark. Because the type constructors [E.expr] and [P.pat]
     are not known to be contractive, OCaml 4 does not allow us to define
     their fixed point as a recursive type abbreviation. In order to work
     around this limitation, we make [closed_pat] a record type. This is
     convenient also because it allows us to explicitly store the gap instead
     of recomputing it every time we transform this closed pattern. *)

  type expr =
    (N.name var, closed_pat) E.expr

  and closed_pat = {
    gap: int;
    pat: (int, expr, expr) P.pat
  }

  (* We also have a type of exposed patterns, where variable holes are filled
     with [N.name]. *)

  type pat =
      (N.name, expr, expr) P.pat

  (* [transform_expr] and [transform_closed_pat] apply a transformation to an
     expression and a closed pattern, while keeping track of how many binders
     have been entered. The parameter [f] is applied at every variable
     occurrence within an expression. *)

  let rec transform_expr (delta : int) (f : int -> N.name var -> (N.name var, closed_pat) E.expr) (e : expr) : expr =
    E.subst
      (f delta)
      (fun p -> transform_closed_pat (delta + p.gap) delta f p)
      e

  and transform_closed_pat (inner : int) (outer : int) (f : int -> N.name var -> (N.name var, closed_pat) E.expr) (p : closed_pat) : closed_pat =
    let pat = p.pat in
    let pat' = 
      P.map
        (fun i -> i)
        (transform_expr inner f)
        (transform_expr outer f)
        pat
    in
    if pat == pat' then
      p
    else
      { gap = p.gap; pat = pat' }

  (* [cons_fresh n rho] produces [n] fresh names and conses them in front
     of the renaming [rho]. *)

  let rec cons_fresh (n : int) (rho : N.name renaming) : N.name renaming =
    if n = 0 then
      rho
    else
      cons_fresh (n - 1) (RandomAccessList.cons (N.fresh()) rho)

  (* [unbind rho e] requires [rho/e] to be 0-closed. Its effect is to apply
     [rho] to [e]. *)

  let unbind (rho : N.name renaming) (e : expr) : expr =
    transform_expr
      0
      (fun delta x -> E.var (apply_shift delta rho x))
      e

  (* [freshen p] opens the abstraction represented by the pattern [p].
     The bound names are replaced with fresh names. The replacement is
     performed within [p] itself and within the sub-expressions found
     in inner holes. *)

  let freshen (p : closed_pat) : pat =
    let rho = cons_fresh p.gap RandomAccessList.empty in
    P.map
      (RandomAccessList.apply rho)
      (unbind rho)
      (fun e -> e)
      p.pat

  (* A closing substitution maps external names to internal indices. It is
     represented as a pair of a map [phi] and an integer [delta], which is
     added to the indices in the codomain of [phi]. *)

  let bind_var (phi : int NameMap.t) (delta : int) (v : N.name var) : (N.name var, _) E.expr =
    E.var (
      match v with
      | External x ->
	  begin try Internal (NameMap.find x phi + delta) with Not_found -> v end
      | Internal _ ->
	  v
    )

  (* [bind phi e] applies [phi] to the expression [e]. *)

  let bind (phi : int NameMap.t) (e : expr) : expr =
    transform_expr 0 (bind_var phi) e

  (* Compute a map of the names that occur in binding position in [p]
     to indices. At the same time, compute the gap. *)

  let bv (p : pat) : int NameMap.t * int =
    let n = ref 0 in
    let phi =
      P.fold
        (fun x phi ->
          if NameMap.mem x phi then phi (* allow non-linear patterns *)
          else let i = !n in n := i + 1; NameMap.add x i phi)
        (fun _ phi -> phi)
        (fun _ phi -> phi)
        p
        NameMap.empty
    in
    phi, !n

  (* Closing an abstraction. *)

  let close (p : pat) : closed_pat =
    let phi, gap = bv p in
    let pat =
      P.map
        (fun x -> NameMap.find x phi)
        (bind phi)
        (fun e -> e)
        p
    in
    { gap; pat }

  (* [subst phi e] applies the substitution [phi], which maps external
     names to 0-closed expressions, to the expression [e]. *)

  let subst_var phi _ v =
    match v with
    | External x ->
        phi x
    | Internal _ ->
        E.var v

  let subst (phi : N.name -> expr) (e : expr) : expr =
    transform_expr 0 (subst_var phi) e

end

