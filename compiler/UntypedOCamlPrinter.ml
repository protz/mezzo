(* This is a pretty-printer for Untyped OCaml. *)

open Hml_Pprint
open UntypedOCaml

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

let rec pattern (p : pattern) : document =
  match p with
  | PVar x ->
      string x
  | PTuple ps ->
      parens_with_nesting (
        separate_map commabreak pattern ps
      )
  | PConstruct (datacon, ps) ->
      string datacon ^^ space ^^ pattern (PTuple ps)
  | PRecord fps ->
      braces_with_nesting (
	separate_map semibreak (fun (field, p) ->
	  (string field ^^ space ^^ equals) ^//^ pattern p
	) fps
      )
  | PAs (p, x) ->
      pattern p ^/^ string "as " ^^ string x
  | PAny ->
      underscore

(*
(* [definition head body cont] prints [head]; prints [body], surrounded
   with spaces and, if necessary, indented by 2; prints the keyword [in];
   breaks a line, if necessary; and prints [cont]. *)
let definition head body cont =
  group (
    group head ^^ jump body ^^ string "in"
  ) ^^ break 1 ^^
  cont
*)
