(* This is a pretty-printer for Untyped OCaml. *)

open Hml_Pprint
open UntypedOCaml

val implementation: implementation -> document
val interface: interface -> document

