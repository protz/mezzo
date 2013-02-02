(* This module puts together the pieces that form the compiler. *)

let ($) x f =
  f x

let ml_file_name (path : string) =
  Filename.chop_suffix path ".mz" ^ ".ml"

let implementation (path : string) (i : SurfaceSyntax.implementation) : unit =
  i
  (* Translate from Mezzo down to Untyped Mezzo. *)
  $ Mezzo2UntypedMezzo.translate_implementation
  (* Translate from Untyped Mezzo down to Untyped OCaml. *)
  $ UntypedMezzo2UntypedOCaml.translate_implementation
  (* Pretty-print. *)
  $ UntypedOCamlPrinter.implementation
  $ Hml_Pprint.dump (ml_file_name path)

