(* This module puts together the pieces that form the compiler. *)

let ($) x f =
  f x

(* The file names used here correspond to the translation of module
   names defined by [UntypedMezzo2UntypedOCaml.translate_module_name]. *)

(* The Mezzo file name [array.mz] becomes the OCaml file name [mzarray.ml]. *)

let translate_file_name (path : string) (extension : string) =
  Filename.dirname path ^
  "/mz_" ^
  Filename.chop_suffix (Filename.basename path) ".mz" ^
  extension

let implementation
    (path : string)
    (impl : SurfaceSyntax.implementation)
    (intf : SurfaceSyntax.interface option)
    : unit =

  (* Define and print the implementation. *)
  (
    impl
      (* Translate from Mezzo down to Untyped Mezzo. *)
      $ Mezzo2UntypedMezzo.translate_implementation
      (* Translate from Untyped Mezzo down to Untyped OCaml. *)
      $ UntypedMezzo2UntypedOCaml.translate_implementation
  ) @ (
    intf
      (* The interface, if present, gives rise to extra implementation items. *)
      $ Option.map Mezzo2UntypedMezzo.translate_interface
      $ UntypedMezzo2UntypedOCaml.translate_interface_as_implementation_filter
   )
  (* Pretty-print. *)
  $ UntypedOCamlPrinter.implementation
  $ MzPprint.dump (translate_file_name path ".ml");

  (* Define and print the interface, if present. *)
  Option.iter (fun intf ->
    intf
      (* Translate from Mezzo down to Untyped Mezzo. *)
      $ Mezzo2UntypedMezzo.translate_interface
      $ UntypedMezzo2UntypedOCaml.translate_interface
      (* Pretty-print. *)
      $ UntypedOCamlPrinter.interface
      $ MzPprint.dump (translate_file_name path ".mli")
  ) intf

