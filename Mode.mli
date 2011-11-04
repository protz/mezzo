(* This module implements modes and their partial ordering. *)

type mode =
  | Duplicable
  | Exclusive
  | Affine

val is_universal: mode -> bool

val leq: mode -> mode -> bool

val show: mode -> string

