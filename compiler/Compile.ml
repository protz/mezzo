(* This module puts together the pieces that form the compiler. *)

let ($) x f =
  f x

let ml_file_name (path : string) =
  Filename.chop_suffix path ".mz" ^ ".ml"

let mli_file_name (path : string) =
  Filename.chop_suffix path ".mz" ^ ".mli"

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
  $ Hml_Pprint.dump (ml_file_name path);

  (* Define and print the interface, if present. *)
  Option.iter (fun intf ->
    intf
      (* Translate from Mezzo down to Untyped Mezzo. *)
      $ Mezzo2UntypedMezzo.translate_interface
      $ UntypedMezzo2UntypedOCaml.translate_interface
      (* Pretty-print. *)
      $ UntypedOCamlPrinter.interface
      $ Hml_Pprint.dump (mli_file_name path)
  ) intf

