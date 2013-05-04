open Signatures

module Make (E : EXPRESSION) : sig

  (* Represents an expression with no free index, i.e., a locally-closed expression. *)
  type 'x expr

  (* Represents a type with one free index. May contain a delayed substitution at the root. *)
  type 'x abstraction

  (* Represents a type with no free index, i.e., a locally-closed type. *)
  type 'x exposed =
    ('x, 'x abstraction) E.expr

  (* Instantiate the free index 0 with a name [x], and allow inspecting the result.
     The delayed substitution at the root (if any) is effectively pushed one level
     down. *)
  val instantiate: 'x abstraction -> 'x -> 'x exposed

  (* Turn an opaque representation into a transparent one. *)
  val expose: 'x expr -> 'x exposed

  (* Turn a transparent representation into an opaque one, forcing any delayed
     substitutions. *)
  val close: 'x exposed -> 'x expr

  (* [bind x t] abstracts away the name [x] in the 0-closed expression [t],
     producing a 1-closed expression. The implementation is eager. *)
  val bind: 'x -> 'x expr -> 'x abstraction

end

