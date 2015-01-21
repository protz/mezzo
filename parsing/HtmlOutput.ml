open Printf
open Buffer
open Lexing

(* Parameters. *)

let b =
  Buffer.create 1024 (* TEMPORARY *)

let nbsp =
  false (* TEMPORARY *)

let charset =
  "iso-8859-1"

let generator =
  "Menhir"

let output_filename =
  "essai.html"

(* Escaping characters within <pre> or <code>. *)

let escape_char c =
  match c with
  | '<'           -> add_string b "&lt;"
  | '>'           -> add_string b "&gt;"
  | '&'           -> add_string b "&amp;"
  | ' ' when nbsp -> add_string b "&nbsp;"
  | c             -> add_char   b c

let escape_string s =
  String.iter escape_char s

(* Printing a Unicode code point. *)

let utf8 (cp : int) =
  bprintf b "&#%d;" cp
    (* TEMPORARY we should print it as an (escaped) ASCII character if
       it is in the ASCII range *)

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
      <meta http-equiv=\"content-type\" content=\"text/html; charset=%s\">\n  \
      <title>%s</title>\n  \
      <meta name=\"GENERATOR\" content=\"%s\">\n  \
      <style type=\"text/css\">\n%s</style>\n\
    </head>\n\
    <body>\n\
    "
    charset title generator style

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
  (* Extract the first and last positions of the array. *)
  let start : int = positions.(0) in
  let finish : int = positions.(n-1) in
  (* Read the file segment comprised between [start] and [finish]. We
     do this inefficiently by reading the entire file again. We assume
     the file is UTF8-encoded. *)
  let data : int array = decode_utf8 (read_whole_file input_filename) in
  (* Open a <pre> tag. Within it, print every character. Add </span><span>
     tags at interesting locations. *)
  pre (fun () ->
    assert (array_search compare positions start = Some 0);
    (* For each location that precedes a character... *)
    for i = start to finish - 1 do
      (* If this is an interesting location, close the previous span
         (if one was opened) and open a new one. *)
      if array_search compare positions i <> None then begin
        if i > start then cspan();
        ospan (pos2span i)
      end;
      (* Print the character at position [i]. *)
      utf8 data.(i)
    done;
    (* There remains to deal with the location [finish]. Close the
       previous span (if one was opened). *)
    if finish > start then cspan()
  )

(* TEMPORARY *)

let essai =
  document_header "Essai" "";
  run2 "/Users/fpottier/dev/menhir/src/IO.ml" [| 0; 100; 200; 300 |];
  document_footer();
  let c = open_out output_filename in
  output_string c (Buffer.contents b);
  close_out c

