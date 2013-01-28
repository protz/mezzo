(* This is a pretty-printer for Untyped OCaml. *)

open SurfaceSyntax
open UntypedOcaml
open Hml_Pprint

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

type pattern =

let rec pattern (p : pattern) : document =
  match p with
  | PVar x ->
      text x
  | PTuple of pattern list
    (* Data constructor pattern. *)
  | PConstruct of string * pattern list
    (* Record pattern. *)
  | PRecord of (string * pattern) list
  | PAs of pattern * string
  | PAny

(* [definition head body cont] prints [head]; prints [body], surrounded
   with spaces and, if necessary, indented by 2; prints the keyword [in];
   breaks a line, if necessary; and prints [cont]. *)
let definition head body cont =
  group (
    group head ^^ jump body ^^ string "in"
  ) ^^ break 1 ^^
  cont
;;

