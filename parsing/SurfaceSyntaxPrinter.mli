open SurfaceSyntax
open MzPprint

(* This is a printer for types in the surface syntax. *)

val print: typ -> document
val p: Buffer.t -> typ -> unit
