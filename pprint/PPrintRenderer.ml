(** A signature for document renderers. *)

module type RENDERER = sig
  
  (** Output channels. *)
  type channel

  (** Documents. *)
  type document

  (** [pretty rfrac width channel document] pretty-prints the document
      [document] into the output channel [channel]. The parameter [width] is
      the maximum number of characters per line. The parameter [rfrac] is the
      ribbon width, a fraction relative to [width]. The ribbon width is the
      maximum number of non-indentation characters per line. *)
  val pretty: float -> int -> channel -> document -> unit

  (** [compact channel document] prints the document [document] to the output
      channel [channel]. No indentation is used. All newline instructions are
      respected, that is, no groups are flattened. *)
  val compact: channel -> document -> unit

end

