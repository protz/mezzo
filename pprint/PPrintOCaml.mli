open PPrintEngine
open PPrintRepresentation

(** A signature for source printers. *)

module type DOCUMENT_REPRESENTATION =
  REPRESENTATION with type representation = document

module ML : DOCUMENT_REPRESENTATION

