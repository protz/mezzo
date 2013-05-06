open Signatures

(* This module defines a locally nameless representation of terms and
   equips it with the standard operations. Its interface is safe in the
   sense that only locally closed terms can be created, i.e., the user
   has no access to the de Bruijn indices that are used internally, and
   cannot cause out-of-range indices to appear. However, the user must
   still be careful not to let a freshly-generated name escape its scope. *)

module Make (N : NAME) (P : PATTERN) (E : EXPRESSION) : sig

  (* -------------------------------------------------------------------------- *)

  (** An opaque type of expressions. *)
  type expr

  (** An opaque type of patterns. A pattern is a binding construct; some
      names are considered bound (hence anonymous) in it. *)
  type abstraction

  (** A transparent type of expressions. An exposed expression presents free
      external names of type [N.name]. Its structure can be examined down to
      the first layer of abstractions, which are opaque. *)
  type exposed_expr =
    (N.name, abstraction) E.expr

  (** A transparent type of patterns. In an exposed pattern, the binding
      positions contain free external names of type [N.name], and the
      sub-expressions in inner and outer positions are exposed. *)
  type exposed_pat =
    (N.name, exposed_expr, exposed_expr) P.pat

  (** Slightly less transparent than [exposed_pat] is [pat], the type of
      patterns whose sub-expressions are opaque. Values of this type can
      be constructed directly by the client and serve as input to the
      function [unexpose_pat]. *)
  type pat =
      (N.name, expr, expr) P.pat

  (* -------------------------------------------------------------------------- *)

  (* Opening. *)

  (** [expose_expr e] produces a transparent representation of the expression [e].
      This representation can be inspected by pattern matching. *)
  val expose_expr: expr -> exposed_expr

  (** [expose_pat a] produces a transparent representation of the abstraction [a],
      where the bound names have been replaced with fresh names. This
      representation can be inspected by pattern matching. *)
  val expose_pat: abstraction -> exposed_pat

  (* -------------------------------------------------------------------------- *)

  (* Closing. *)

  (** [unexpose_expr] turns one layer of transparent expression structure back
      to an opaque representation. *)
  val unexpose_expr: exposed_expr -> expr

  (** [unexpose_pat] turns one layer of transparent pattern structure back to
      an opaque representation. The free names in binding positions become
      bound. *)
  val unexpose_pat: pat -> abstraction

  (* -------------------------------------------------------------------------- *)

  (* A substitution maps external names to expressions. *)

  type substitution =
    N.name -> expr

  (** [subst_expr psi e] applies the substitution [psi] to the expression [e]. *)
  val subst_expr: substitution -> expr -> expr

end

