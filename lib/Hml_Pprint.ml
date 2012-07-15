(** This modules exports a modified version of {!Pprint} with extra printers. *)

include Pprint

(* Some Bash-isms *)

type colors = {
  mutable green: document;
  mutable red: document;
  mutable blue: document;
  mutable yellow: document;
  mutable default: document;
  mutable underline: document;
}

let colors = {
  green = empty;
  red = empty;
  blue = empty;
  yellow = empty;
  default = empty;
  underline = empty;
}

let enable_colors () =
  colors.green <- fancystring Bash.colors.Bash.green 0;
  colors.red <- fancystring Bash.colors.Bash.red 0;
  colors.blue <- fancystring Bash.colors.Bash.blue 0;
  colors.yellow <- fancystring Bash.colors.Bash.yellow 0;
  colors.default <- fancystring Bash.colors.Bash.default 0;
  colors.underline <- fancystring Bash.colors.Bash.underline 0;
;;

let disable_colors () =
  colors.green <- empty;
  colors.red <- empty;
  colors.blue <- empty;
  colors.yellow <- empty;
  colors.default <- empty;
  colors.underline <- empty;
;;

let _ =
  enable_colors ()

let arrow =
  string "->"
;;

let semisemi =
  semi ^^ semi
;;

let ccolon =
  colon ^^ colon
;;

let int i =
  string (string_of_int i)
;;

let larrow =
  string "<-"
;;

let slash =
  string "/"
;;

let utf8_length s =
  (* Stolen from Batteries *)
  let rec length_aux s c i =
    if i >= String.length s then c else
    let n = Char.code (String.unsafe_get s i) in
    let k =
      if n < 0x80 then 1 else
      if n < 0xe0 then 2 else
      if n < 0xf0 then 3 else 4
    in
    length_aux s (c + 1) (i + k)
  in
  length_aux s 0 0
;;

let print_string s =
  fancystring s (utf8_length s)
;;

let name_gen count =
  (* Of course, won't work nice if more than 26 type parameters... *)
  let alpha = "α" in
  let c0 = Char.code alpha.[1] in
  Hml_List.make count (fun i ->
    let code = c0 + i in
    Printf.sprintf "%c%c" alpha.[0] (Char.chr code)
  )
;;

(* [heading head body] prints [head]; breaks a line and indents by 2,
 if necessary; then prints [body]. *)
let heading head body =
  group (
    nest 2 (
      group head ^^ linebreak ^^
      body
    )
  )
;;

(* [jump body] either displays a space, followed with [body], followed
   with a space, all on a single line; or breaks a line, prints [body]
   at indentation 2. *)
let jump ?(indent=2) body =
  group (nest indent (line ^^ body))
;;

(* [definition head body cont] prints [head]; prints [body], surrounded
   with spaces and, if necessary, indented by 2; prints the keyword [in];
   breaks a line, if necessary; and prints [cont]. *)
let definition head body cont =
  group (
    group head ^^ jump body ^^ text "in"
  ) ^^ line ^^
  cont
;;

(* [join sep (s1 :: s2 :: ... :: sn)] returns
 * [s1 ^^ sep ^^ s2 ^^ ... ^^ sep ^^ sn] *)
let join sep strings =
  match strings with
  | hd :: tl ->
      List.fold_left (fun sofar s -> sofar ^^ sep ^^ s) hd tl
  | [] ->
      empty
;;

(* [join_left sep (s1 :: s2 :: ... :: sn)] returns
 * [sep ^^ s1 ^^ sep ^^ s2 ^^ ... ^^ sep ^^ sn] *)
let join_left sep strings =
  List.fold_left (fun sofar s -> sofar ^^ sep ^^ s) empty strings
;;

let rec english_join = function
  | [] ->
      empty
  | e :: [] ->
      e
  | e1 :: e2 :: [] ->
      e1 ^^ string " and " ^^ e2
  | hd :: tl ->
      hd ^^ string ", " ^^ english_join tl
;;

let render doc =
  let buf = Buffer.create 16 in
  Pprint.PpBuffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
