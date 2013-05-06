open Signatures

module Make (N : NAME) (P : PATTERN) (E : EXPRESSION) : sig

  (* Represents an expression with no free index, i.e., a locally-closed expression. *)
  type expr

  (* Represents an expression with one free index. May contain a delayed substitution at the root. *)
  type abstraction

  (* Represents an expression with no free index, i.e., a locally-closed expression. *)
  type exposed_expr =
    (N.name, abstraction) E.expr

  (* Represents a pattern with no free index, i.e., a locally-closed pattern. *)
  type exposed_pat =
    (N.name, exposed_expr, exposed_expr) P.pat

  (* Instantiate the bound names with fresh names, and allow inspecting the result.
     The delayed substitution at the root (if any) is effectively pushed one level
     down. *)
  val instantiate: abstraction -> exposed_pat

  (* Turn an opaque representation into a transparent one. *)
  val expose: expr -> exposed_expr

  (* Turn a transparent representation into an opaque one, forcing any delayed
     substitutions. *)
  val close_exposed_expr: exposed_expr -> expr

  (* [bind] abstracts away the bound names. The implementation is eager. *)
  val bind: exposed_pat -> abstraction

end

