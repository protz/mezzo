open Printf
open Buffer

(* Parameters. *)

let b =
  Buffer.create 1024 (* TEMPORARY *)

let nbsp =
  false (* TEMPORARY *)

let charset =
  "iso-8859-1"

let generator =
  "Menhir"

let filename =
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

(* TEMPORARY *)

let essai =
  document_header "Essai" "";
  pre (fun () ->
    escape_string "if x < 0 then true else false"
  );
  document_footer();
  let c = open_out filename in
  output_string c (Buffer.contents b);
  close_out c

(*

We expect:
  a source file name (or directly its contents)
  a bunch of locations of interest
We perform:
  sort the locations by cnum, place them in a sorted array
  deduce the source code interval that we need to display (extending it to the beginning of the first line)
  print this interval within <pre>, inserting </span><span class="i"> at every location i of interest
    plus one <span> at the beginning and one </span> at the end
  set up a function that converts a pair of locations of interest to a list of span names
    logarithmic search in the array should do
We expect:
  a table containing text fragments plus indications that some fragments are associated with a pair of locations
We perform:
  convert to HTML table
  emitting div with fresh ids for the fragments
  and building up a css table on the side, mapping div ids to lists of spans that should change color on mouseover
*)

(* [array_search] implements logarithmic-time search in a sorted array. [cmp]
   is the ordering function. [a] is the array, which must be sorted, and may
   contain duplicate elements. [lo] and [hi] determine the semi-open interval
   within which we are searching. [v] is the value we are looking for; it must
   appear in the search interval. The function returns an index at which [v]
   is found. *)

let rec array_search cmp a lo hi v =
  (* Because [v] appears in the array, the interval between [lo]
     and [hi] cannot be empty. *)
  assert (lo < hi);
  (* If this interval has just one element, then it must be [v],
     and we are done. *)
  if lo + 1 = hi then begin
    assert (cmp a.(lo) v = 0);
    lo
  end
  (* Otherwise, split it in the middle, and look for [v] on the
     appropriate side. *)
  else
    let mid = lo + (hi - lo) / 2 in
    assert (lo < mid && mid < hi);
    let c = cmp a.(mid) v in
    if c = 0 then
      mid
    else if c < 0 then
      array_search cmp a mid hi v
    else
      array_search cmp a lo mid v

let array_search cmp a v =
  array_search cmp a 0 (Array.length a) v

