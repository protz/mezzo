open Signatures

module Make (N : NAME) (P : PATTERN) (E : EXPRESSION) = struct

  (* -------------------------------------------------------------------------- *)

  (* A variable is either external (a name) or internal (a de Bruijn index). *)

  type var =
    | External of N.name
    | Internal of int

  (* -------------------------------------------------------------------------- *)

  (* An opening substitution is an (injective) mapping of internal names to
     external names. Such a substitution is used when opening an abstraction
     (i.e., unbinding). *)

  type opening =
    N.name RandomAccessList.t

  (* The empty opening. *)

  let empty =
    RandomAccessList.empty

  (* [extend n rho] produces [n] fresh names and conses them in front of the
     opening [rho]. *)

  let rec extend (n : int) (rho : opening) : opening =
    if n = 0 then
      rho
    else
      extend (n - 1) (RandomAccessList.cons (N.fresh()) rho)

  (* [open_var_zero rho v] applies the opening [rho] to the variable [v]. We
     assume that the variable [v] is either external or in the domain of
     [rho]. The result is an external name, which we wrap as an expression.
     The suffix [zero] suggests that this is a special case where [delta]
     is zero. *)

  let open_var_zero (rho : opening) (v : var) : (N.name, _) E.expr =
    E.var (
      match v with
      | Internal i ->
          (* By assumption, the domain of [rho] includes [i], so we apply [rho]
             without fear. *)
        RandomAccessList.apply rho i
      | External x ->
          (* An external name is unaffected. *)
        x
    )

  (* [open_var rho delta v] applies the opening [rho], shifted up by
     [delta], to the variable [v]. We assume that the variable [v] is either
     external or in the domain of [rho^delta]. The result is an external or
     internal name, which we wrap as an expression. *)

  let open_var (rho : opening) (delta : int) (v : var) : (var, _) E.expr =
    E.var (
      match v with
      | Internal i when i >= delta ->
          (* By assumption, the domain of [rho] includes [i - delta], so we apply
             [rho] without fear. *)
          External (RandomAccessList.apply rho (i - delta))
      | _ ->
          (* An external name, or an internal name below [delta], is unaffected. *)
          v
    )

  (* -------------------------------------------------------------------------- *)

  (* A closing substitution maps external names to internal indices. It is
     represented as a pair of a map [phi] and an integer [delta], which is
     added to the indices in the codomain of [phi]. It behaves as the
     identity outside of the domain of [phi]. *)

  (* [close_var phi delta v] applies the closing [phi], shifted up by [delta],
     to the variable [v]. The result is an external or internal name, which we
     wrap as an expression. *)

  let close_var (phi : int N.Map.t) (delta : int) (v : var) : (var, _) E.expr =
    E.var (
      match v with
      | Internal _ ->
	  v
      | External x ->
	  try Internal (N.Map.find x phi + delta) with Not_found -> v
    )

  (* -------------------------------------------------------------------------- *)

  (* The locally nameless representation of expressions is obtained by filling
     variable holes with [var] and by filling pattern holes with [closed_pat].
     In closed patterns, variable holes are filled with [int] and inner and
     outer expression holes are filled with [expr]. *)

  (* In the definition of [closed_pat], we could choose to fill variable holes
     with [unit]. This would yield a representation where bound names are
     anonymous. The present definition allows non-linear patterns, i.e.,
     patterns where a name occurs several times. We adopt the convention that,
     once an abstraction has been closed, the names that occur in the pattern
     form an interval of the form [0, n), for some value of [n], which is less
     than or equal to the number of variable holes in the pattern. We refer to
     [n] as the gap. We note that the order in which the bound names are
     numbered (say, left-to-right, or right-to-left) is not relevant. *)

  (* Because the type constructors [E.expr] and [P.pat] are not known to be
     contractive, OCaml 4 does not allow us to define their fixed point as a
     recursive type abbreviation. In order to work around this limitation, we
     make [closed_pat] a record type. We take this opportunity to explicitly
     store the gap instead of recomputing it every time we transform this
     closed pattern. *)

  type expr =
    (var, closed_pat) E.expr

  and closed_pat = {
    gap: int;
    pat: (int, expr, expr) P.pat
  }

  (* There is also a type of opened patterns, where variable holes are filled
     with [N.name]. This representation is obtained after an abstraction has
     been opened. *)

  type pat =
      (N.name, expr, expr) P.pat

  (* -------------------------------------------------------------------------- *)

  (* [transform_expr] applies a transformation, represented by the function
     [f], to every variable occurrence within an expression. The parameter
     [delta] keeps track of how many binders have been entered. The function
     [f] is itself parameterized over [delta]. *)

  let rec transform_expr (delta : int) (f : int -> var -> expr) (e : expr) : expr =
    E.subst
      (* At variable occurrences, apply [f]. *)
      (f delta)
      (* At abstractions, apply [transform_closed_pat], using [delta + p.gap]
	 as the updated value of [delta] for those expressions that lie within
	 the scope of the pattern. The value of [delta] remains unchanged for
	 those expressions that lie outside the scope of the pattern. *)
      (fun p -> transform_closed_pat (delta + p.gap) delta f p)
      e

  and transform_closed_pat (inner : int) (outer : int) f (p : closed_pat) : closed_pat =
    let pat = p.pat in
    let pat' =
      P.map
	(* At bound variable occurrences, do nothing. *)
        (fun i -> i)
	(* At sub-expressions, apply [transform_expr] with a suitable
	   value of [delta]. *)
        (transform_expr inner f)
        (transform_expr outer f)
        pat
    in
    (* If possible, preserve sharing. The gap is unchanged. *)
    if pat == pat' then p else { gap = p.gap; pat = pat' }

  (* -------------------------------------------------------------------------- *)

  (* [open_expr rho delta e] requires the domain of [rho^delta] to cover the
     free internal names of [e]. Its effect is to apply [rho^delta] to [e]. *)

  let open_expr (rho : opening) (delta : int) (e : expr) : expr =
    transform_expr delta (open_var rho) e

  (* [open_pat p] opens the closed pattern [p]. The bound names of [p] are
     replaced with fresh names. The replacement is performed within [p] itself
     and within the sub-expressions found in inner holes. *)

  let open_pat (p : closed_pat) : pat =
    (* Create as many fresh names as dictated by [p.gap]. *)
    let rho = extend p.gap empty in
    P.map
      (* Replace each bound name with the corresponding fresh name. *)
      (RandomAccessList.apply rho)
      (* Apply this opening substitution to the inner expressions. *)
      (open_expr rho 0)
      (* Do not touch the outer expressions. *)
      (fun e -> e)
      p.pat

  (* -------------------------------------------------------------------------- *)

  (* [close_expr phi e] applies the closing [phi] to the expression [e]. *)

  let close_expr (phi : int N.Map.t) (e : expr) : expr =
    transform_expr 0 (close_var phi) e

  (* [bv p] returns a map of the names that occur in binding position in
     the pattern [p] to indices in the interval [0, n), where [n] is the
     gap of [p]. It also computes and returns [n]. *)

  let bv (p : (N.name, _, _) P.pat) : int N.Map.t * int =
    let n = ref 0 in
    let phi =
      P.fold
        (fun x phi ->
	  (* We allow non-linear patterns, so if a name has already been
	     encountered, we skip it without generating a new index. *)
          if N.Map.mem x phi then
	    phi
          else begin
	    let i = !n in n := i + 1; N.Map.add x i phi
	  end)
        (fun _ phi -> phi)
        (fun _ phi -> phi)
        p
        N.Map.empty
    in
    phi, !n

  (* [close_pat p] closes the pattern [p]. The names that appear in
     binding position become anonymous, within [p] itself and within
     the sub-expressions that lie within the scope of the pattern. *)

  let close_pat (p : pat) : closed_pat =
    (* Create a closing substitution. Compute the gap. *)
    let phi, gap = bv p in
    let pat =
      P.map
	(* A name in binding position is replaced with the corresponding
	   de Bruijn index. *)
        (fun x -> N.Map.find x phi)
	(* The closing [phi] is applied to an inner expression. *)
        (close_expr phi)
	(* An outer expression is unaffected. *)
        (fun e -> e)
        p
    in
    { gap; pat }

  (* -------------------------------------------------------------------------- *)

  (* A substitution maps external names to 0-closed expressions. *)

  type substitution =
    N.name -> expr

  (* [subst_var psi delta v] applies the substitution [psi] to the variable [v].
     The parameter [delta] is ignored, since internal names are unaffected by
     the substitution anyway. *)

  let subst_var (psi : substitution) _ (v : var) : expr =
    match v with
    | External x ->
        psi x
    | Internal _ ->
        E.var v

  (* [subst_expr psi e] applies the substitution [psi] to the expression [e]. *)

  let subst_expr (psi : substitution) (e : expr) : expr =
    transform_expr 0 (subst_var psi) e

  (* -------------------------------------------------------------------------- *)

  (* An abstraction is the suspended application of a opening to a closed
     pattern. *)

  type abstraction = {
    rho: opening;
    p  : closed_pat;
  }

  (* In the exposed (or transparent) representation of expressions, variable
     holes are filled with [N.name], as opposed to [var], which means that
     only external names are visible to the client. Furthermore, pattern holes
     are filled with [abstraction], which means that there is a suspended
     opening at each binding site in the first layer. *)

  type exposed_expr =
    (N.name, abstraction) E.expr

  (* In the exposed representation of patterns, only external names are visible,
     and inner and outer holes contain exposed expressions. *)

  type exposed_pat =
    (N.name, exposed_expr, exposed_expr) P.pat

  (* [attack rho e] requires that the domain of [rho] include [e], or in
     other words, that [rho/e] be 0-closed. Its effect is to apply [rho]
     to [e], stopping at the first layer of binders, hence producing an
     exposed expression. *)

  let trivial (p : closed_pat) : abstraction =
    { rho = RandomAccessList.empty; p }

  let suspend rho (p : closed_pat) : abstraction =
    { rho; p }

  let attack_expr (rho : opening) (e : expr) : exposed_expr =
    E.subst
      (open_var_zero rho)
      (suspend rho)
      e

  let expose (e : expr) : exposed_expr =
    attack_expr RandomAccessList.empty e

  let instantiate ({ rho = outer; p } : abstraction) : exposed_pat =
    let inner = extend p.gap outer in
    P.map
      (RandomAccessList.apply inner)
      (attack_expr inner)
      (attack_expr outer)
      p.pat

  let force ({ rho; p } : abstraction) : closed_pat =
    (* Recognize the special case where [rho] is the identity. This could be important
       because we sometimes build a trivial abstraction. *)
    if RandomAccessList.is_empty rho then
      p
    else
      (* Perform an eager opening. *)
      let pat' =
        P.map
          (fun i -> i)
          (open_expr rho p.gap)
          (open_expr rho 0)
          p.pat
      in
      { gap = p.gap; pat = pat' }

  let close_exposed_expr (e : exposed_expr) : expr = (* 0-closed *)
    E.subst
      (fun v -> E.var (External v))
      force
      e

  let close_exposed_pat (p : exposed_pat) : pat =
    P.map
      (fun x -> x)
      close_exposed_expr
      close_exposed_expr
      p

  let bind (p : exposed_pat) : abstraction =
    trivial (close_pat (close_exposed_pat p))

end

