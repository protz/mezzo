open Signatures

(* A unary binder consists of just one variable hole and one inner
   expression hole, i.e., this expression is in the scope of this
   binder. *)

include PATTERN with type ('x, 'i, 'o) pat =
  'x * 'i
