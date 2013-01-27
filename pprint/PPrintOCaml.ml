open PPrintEngine
open PPrintCombinators
open PPrintRepresentation

let sprintf fmt = Printf.ksprintf arbitrary_string fmt

module type DOCUMENT_REPRESENTATION =
  REPRESENTATION with type representation = document

(* please remove as soon as this will be available in ocaml *)
module MissingFloatRepr = struct
  let valid_float_lexeme s =
    let l = String.length s in
    let rec loop i =
      if i >= l then s ^ "." else
      match s.[i] with
      | '0' .. '9' | '-' -> loop (i+1)
      | _ -> s
    in loop 0

  let float_repres f =
    match classify_float f with
      FP_nan -> "nan"
    | FP_infinite ->
        if f < 0.0 then "neg_infinity" else "infinity"
    | _ ->
        let s1 = Printf.sprintf "%.12g" f in
        if f = float_of_string s1 then valid_float_lexeme s1 else
        let s2 = Printf.sprintf "%.15g" f in
        if f = float_of_string s2 then valid_float_lexeme s2 else
        Printf.sprintf "%.18g" f
end

(* TEMPORARY avoid List.map *)
module ML = struct
let seq1 opening separator closing =
  surround_separate 2 0 (opening ^^ closing) opening (separator ^^ break 1) closing
let seq2 opening separator closing =
  surround_separate 2 1 (opening ^^ closing) opening (separator ^^ break 1) closing

  type representation = document
  let tuple = seq1 lparen comma rparen
  let variant _ cons _ args =
    if args = [] then !^cons else !^cons ^^ tuple args
  let record _ fields =
    seq2 lbrace semi rbrace (List.map (fun (k, v) -> infix 2 1 equals !^k v) fields)
  let option f = function
    | Some x -> !^"Some" ^^ tuple [f x]
    | None -> !^"None"
  let list f xs = seq2 lbracket semi rbracket (List.map f xs)
  let lbracketbar = string "[|"
  let rbracketbar = string "|]"
  let array f xs = seq2 lbracketbar semi rbracketbar (Array.to_list (Array.map f xs))
  let ref f x = record "ref" ["contents", f !x]
  let float f = arbitrary_string (MissingFloatRepr.float_repres f)
  let int = sprintf "%d"
  let int32 = sprintf "%ld"
  let int64 = sprintf "%Ld"
  let nativeint = sprintf "%nd"
  let char = sprintf "%C"
  let bool = sprintf "%B"
  let string = sprintf "%S"
  let unknown tyname _ = sprintf "<abstr:%s>" tyname
end

