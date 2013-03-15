(* This is a pretty-printer for Untyped OCaml. *)

open MzPprint
open UntypedOCaml

val implementation: implementation -> document
val interface: interface -> document

