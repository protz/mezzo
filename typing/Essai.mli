type ('var, 'scope) ty =
| TyVar of 'var
| TyAtom
| TyArrow of ('var, 'scope) ty * ('var, 'scope) ty
| TyQ of 'scope

val map: ('var1 -> 'var2) -> ('scope1 -> 'scope2) -> ('var1, 'scope1) ty -> ('var2, 'scope2) ty

(* Represents a type with no free index, i.e., a locally-closed type. *)
type 'x term

(* Represents a type with one free index. May contain a delayed substitution at the root. *)
type 'x abstraction

(* Represents a type with no free index, i.e., a locally-closed type. *)
type 'x exposed =
  ('x, 'x abstraction) ty

(* Instantiate the free index 0 with a name [x], and allow inspecting the result.
   The delayed substitution at the root (if any) is effectively pushed one level
   down. *)
val instantiate: 'x abstraction -> 'x -> 'x exposed

(* Turn an opaque representation into a transparent one. *)
val expose: 'x term -> 'x exposed

(* Turn a transparent representation into an opaque one, forcing any delayed
   substitutions. *)
val close: 'x exposed -> 'x term

(* [abstract x t] abstracts away the name [x] in the 0-closed term [t],
   producing a 1-closed term. The implementation is eager. *)
val abstract: 'x -> 'x term -> 'x abstraction

