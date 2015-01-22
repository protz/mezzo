open Printf
open Buffer
open Lexing

(* --------------------------------------------------------------------------- *)

(* The syntax error messages that we wish to render have the following
   structure. *)

type message = {
  (* A file name. For simplicity, we currently re-read the file. *)
  msg_filename: string;
  (* A list of explanations. *)
  msg_explanations: explanation list
}

and explanation = {
  (* A past. This is a list of words (terminal and non-terminal symbols,
     really), each of which is linked to a range of the input file.
     They represent what we have understood so far. *)
  past: (word * position * position) list;
  (* A future. This is a list of words (symbols, really). They represent
     what we expect to read next. *)
  future: word list;
  (* A goal (a non-terminal symbol). It represents the reduction that we
     will perform if we read this future. *)
  goal: word
}

and word =
    string

(* --------------------------------------------------------------------------- *)

(* Parameters. *)

let b =
  Buffer.create 1024 (* TEMPORARY *)

(* Escaping characters within <pre> or <code>. *)

let escape_char c =
  match c with
  | '<' -> add_string b "&lt;"
  | '>' -> add_string b "&gt;"
  | '&' -> add_string b "&amp;"
  | c   -> add_char   b c

let escape_string s =
  String.iter escape_char s

(* Printing a Unicode code point. *)

let utf8 (cp : int) =
  if cp <= 0x7f then
    escape_char (Char.chr cp)
  else
    bprintf b "&#%d;" cp

(* Opening and closing tags. *)

let otag tag attributes =
  bprintf b "<%s" tag;
  List.iter (fun (attribute, value) ->
    bprintf b " %s=\"%s\"" attribute value
  ) attributes;
  bprintf b ">"

let ctag tag =
  bprintf b "</%s>" tag

(* Opening and closing <span> tags. *)

let ospan c =
  otag "span" [ "class", c ]

let cspan () =
  ctag "span"

let span c f =
  ospan c; f(); cspan()

(* <div> tags. *)

let div id f =
  otag "div" [ "id", id ]; f(); ctag "div"

(* <pre> tags. *)

let pre f =
  otag "pre" []; f(); ctag "pre"

(* Printing a line number. *)

let line_number b i =
  span "Clinenum" (fun () ->
    bprintf b "%4d: " i
  )

(* Printing a document header and footer. *)

let document_header title style =
  bprintf b "\
    <!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01//EN\" \
    \"http://www.w3.org/TR/html4/strict.dtd\">\n\
    <html>\n\
    <head>\n  \
      <meta http-equiv=\"content-type\" content=\"text/html; charset=us-ascii\">\n  \
      <title>%s</title>\n  \
      <style type=\"text/css\">\n%s</style>\n\
    </head>\n\
    <body>\n\
    "
    title style

let document_footer () =
  bprintf b "</body>\n</html>\n"

(*

We expect:
  a source file name (or directly its contents)
  a bunch of positions of interest
We perform:
  sort the positions by cnum, place them in a sorted array
  deduce the source code interval that we need to display (extending it to the beginning of the first line)
  print this interval within <pre>, inserting </span><span class="i"> at every position i of interest
    plus one <span> at the beginning and one </span> at the end
  set up a function that converts a pair of positions of interest to a list of span names
    logarithmic search in the array should do
We expect:
  a table containing text fragments plus indications that some fragments are associated with a pair of positions
We perform:
  convert to HTML table
  emitting div with fresh ids for the fragments
  and building up a css table on the side, mapping div ids to lists of spans that should change color on mouseover
*)

(* [array_search] implements logarithmic-time search in a sorted array. [cmp]
   is the ordering function. [a] is the array, which must be sorted, and may
   contain duplicate elements. [lo] and [hi] determine the semi-open interval
   within which we are searching. [v] is the value we are looking for; it may
   or may not appear in the search interval. The function returns an index at
   which [v] is found, or nothing. *)

let rec array_search cmp a lo hi v =
  assert (lo <= hi);
  (* If the interval is empty, fail. *)
  if lo = hi then
    None
  (* Otherwise, split the interval in the middle, and look for [v] at the
     middle or on the appropriate side. *)
  else
    let mid = lo + (hi - lo) / 2 in
    assert (lo <= mid && mid < hi);
    let c = cmp a.(mid) v in
    if c = 0 then
      Some mid
    else if c < 0 then
      array_search cmp a (mid + 1) hi v
    else
      array_search cmp a lo mid v

let array_search cmp a v =
  array_search cmp a 0 (Array.length a) v

(* Copied from Menhir's IO. *)

let chunk_size =
  16384

let exhaust channel =
  let buffer = Buffer.create chunk_size in
  let chunk = Bytes.create chunk_size in
  let rec loop () =
    let length = input channel chunk 0 chunk_size in
    if length = 0 then
      Buffer.contents buffer
    else begin
      Buffer.add_subbytes buffer chunk 0 length;
      loop()
    end
  in
  loop()

let read_whole_file filename =
  let channel = open_in filename in
  let s = exhaust channel in
  close_in channel;
  s

(* We assume the file is UTF8-encoded and decode it to an array of integer
   code points. *)

let decode_utf8 (data : string) : int array =
  Utf8.to_int_array data 0 (String.length data)

(* [compare_positions] compares two source code positions. We assume they
   originate in the same source file. If they don't (perhaps because some
   form of #include is being used), then a more complex form of comparison
   may be required. *)

let compare_positions pos1 pos2 =
  assert (pos1.pos_fname == pos2.pos_fname);
  compare pos1.pos_cnum pos2.pos_cnum

(* A conventional way of converting a position to a span class. *)
let pos2span =
  string_of_int

let rec run (input_filename : string) (positions : position list) =
  assert (positions <> []);
  (* Sort the list of positions and remove duplicate elements. *)
  let positions = MenhirLib.General.weed compare_positions positions in
  (* Extract the first position of the list, which tells us how far back
     in the code we should go in order to explain the syntax error.
     Extend it a little further back to the beginning of its line,
     and this new position to the head of the list, if needed. *)
  let positions =
    let start = List.hd positions in
    if start.pos_bol = start.pos_cnum then
      positions
    else
      { start with pos_cnum = start.pos_bol } :: positions
  in
  (* Turn the list of positions into an array of integers. *)
  let positions = Array.of_list positions in
  let positions = Array.map (fun pos -> pos.pos_cnum) positions in
  run2 input_filename positions

and run2 input_filename positions =
  let n = Array.length positions in
  (* Read the whole file again. Reading the file segment comprised between
     the start and end positions would suffice, but that is not so easy,
     considering the file is UTF-8 encoded and CRLF conversion might be
     taking place. *)
  let data : int array = decode_utf8 (read_whole_file input_filename) in
  (* Open a <pre> tag. Within it, print the file segment of interest, adding
     <span> and </span> tags at appropriate locations. *)
  pre (fun () ->
    (* We have [n] locations of interest, hence [n-1] spans. *)
    for i = 0 to n-2 do
      span (pos2span positions.(i)) (fun () ->
        (* Within each span, print raw characters. *)
        for j = positions.(i) to positions.(i+1)-1 do
          utf8 data.(j)
        done
      )
    done
  )

(* TEMPORARY *)

let essai =
  document_header "Essai" "";
  run2 "/Users/fpottier/dev/menhir/src/IO.ml" [| 0; 100; 200; 300 |];
  document_footer();
  let output_filename = "essai.html" in
  let c = open_out output_filename in
  output_string c (Buffer.contents b);
  close_out c

