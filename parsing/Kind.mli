(* Kinds. *)

(* Arrow kinds are not accessible to the user. They are used internally:
   a user-defined algebraic data type constructor receives an arrow kind.
   Thus, even internally, we only use first-order kinds (that is, the
   left-hand argument of an arrow kind is never itself an arrow kind). *)

type kind =
  | KValue
  | KType
  | KPerm
  | KArrow of kind * kind

(* [karrow] helps build an [n]-ary arrow. *)
val karrow: ('a * kind) list -> kind -> kind

(** [as_arrow k] transforms the kind [k] to an [n]-ary arrow kind. This
    is permitted for every kind [k]. A non-arrow kind is viewed as an
    arrow kind of arity 0. *)
val as_arrow: kind -> kind list * kind

(** [arity k] is the arity of [k], viewed as an arrow kind. *)
val arity: kind -> int

(** [print] and [print_kind] convert a kind to a textual representation. *)
val print: kind -> string
val print_kind: kind -> PPrint.document

(** [equal] tests the equality of two kinds. *)
val equal: kind -> kind -> bool
