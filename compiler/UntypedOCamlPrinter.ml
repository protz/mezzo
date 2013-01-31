(* This is a pretty-printer for Untyped OCaml. *)

open Hml_Pprint
open UntypedOCaml

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

let rec simple_pattern (p : pattern) : document =
  match p with
  | PVar x ->
      utf8string x
  | PAny ->
      underscore
  | PTuple ps ->
      parens_with_nesting (
        separate_map commabreak pattern ps
      )
  | PRecord fps ->
      braces_with_nesting (
	separate_map semibreak (fun (field, p) ->
	  (utf8string field ^^ space ^^ equals) ^//^ pattern p
	) fps
      )
  | PConstruct _
  | PAs _ ->
      parens_with_nesting (pattern p)

and pattern p =
  match p with
  | PConstruct (datacon, ps) ->
      utf8string datacon ^^ space ^^ simple_pattern (PTuple ps)
  | PAs (p, x) ->
      pattern p ^/^ string "as " ^^ utf8string x
  | _ ->
      simple_pattern p

(* ---------------------------------------------------------------------------- *)




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
