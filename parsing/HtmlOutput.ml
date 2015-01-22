open Printf
open Buffer
open Lexing
open MenhirLib.ErrorReporting

(* For convenience, we use a global buffer. *)

let b =
  Buffer.create 4096

(* Escaping characters within <pre>, etc. *)

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

let raw_tag tag attributes content =
  bprintf b "<%s" tag;
  attributes();
  bprintf b ">";
  content();
  bprintf b "</%s>" tag

let tag tag attributes content =
  raw_tag tag (fun () ->
    List.iter (fun (attribute, value) ->
      bprintf b " %s=\"%s\"" attribute value
    ) attributes
  ) content

(* <span>. *)

let span id f =
  tag "span" [ "id", id ] f

(* <div>, causing another element to by highlighted. *)

let chbg target color =
  bprintf b "chbg('%s', '%s');" target color

let div targets color content =
  raw_tag "span" (fun () ->
    bprintf b " onmouseover=\"";
    targets (fun target -> chbg target color);
    bprintf b "\"";
    bprintf b " onmouseout=\"";
    targets (fun target -> chbg target "white");
    bprintf b "\"";
  ) content

(* <table> *)

let th classe content =
  tag "th" [ "class", classe ] content

let td classe content =
  tag "td" [ "class", classe ] content

let tr content =
  tag "tr" [] content

let table head body =
  tag "table" [] (fun () ->
    tag "thead" [] head;
    tag "tbody" [] body
  )

(* Printing a line number. *)

let line_number b i =
  span "Clinenum" (fun () ->
    bprintf b "%4d: " i
  )

(* Printing a document header and footer. *)

let document_header title style script =
  bprintf b "\
    <!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01//EN\" \
    \"http://www.w3.org/TR/html4/strict.dtd\">\n\
    <html>\n\
    <head>\n  \
      <meta http-equiv=\"content-type\" content=\"text/html; charset=us-ascii\">\n  \
      <title>%s</title>\n  \
      <style type=\"text/css\">\n%s</style>\n\
      <script>\n%s</script>\n\
    </head>\n\
    <body>\n\
    "
    title style script

let document_footer () =
  bprintf b "</body>\n</html>\n"

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

let success o =
  match o with
  | None ->
      assert false
  | Some x ->
      x

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

let run print_symbol filename explanations =
  assert (explanations <> []);
  (* Gather all positions. *)
  let positions : position list =
    List.fold_left (fun accu { past; _ } ->
      assert (past <> []);
      List.fold_left (fun accu (_, pos1, pos2) ->
        pos1 :: pos2 :: accu
      ) accu past
    ) [] explanations
  in
  (* Make sure the positions seem reasonable. *)
  assert (positions <> []);
  List.iter (fun pos ->
    assert (pos.pos_bol >= 0);
    assert (pos.pos_cnum >= 0)
  ) positions;
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
  let n = Array.length positions in
  (* Define a function that allows iterating on the spans comprised
     between [pos1] and [pos2]. *)
  let between pos1 pos2 f =
    let pos1 = pos1.pos_cnum
    and pos2 = pos2.pos_cnum in
    assert (pos1 <= pos2);
    let i1 = success (array_search compare positions pos1)
    and i2 = success (array_search compare positions pos2) in
    assert (i1 <= i2);
    for i = i1 to i2-1 do
      f (pos2span positions.(i))
    done
  in
  (* Read the whole file again. Reading the file segment comprised between
     the start and end positions would suffice, but that is not so easy,
     considering the file is UTF-8 encoded and CRLF conversion might be
     taking place. *)
  let data : int array = decode_utf8 (read_whole_file filename) in
  (* Check that all positions exist in the file. *)
  assert (positions.(n) < Array.length data);
  (* Open a <pre> tag. Within it, print the file segment of interest, adding
     <span> and </span> tags at appropriate locations. *)
  tag "pre" [] (fun () ->
    (* We have [n] locations of interest, hence [n-1] spans. *)
    for i = 0 to n-2 do
      span (pos2span positions.(i)) (fun () ->
        (* Within each span, print raw characters. *)
        for j = positions.(i) to positions.(i+1)-1 do
          utf8 data.(j)
        done
      )
    done
  );
  (* Print the explanations. *)
  table (fun () ->
    tr (fun () ->
      th "past" (fun () ->
        escape_string "We have recognized this:"
      );
      th "future" (fun () ->
        escape_string "We expect this:"
      );
      th "goal" (fun () ->
        escape_string "So as to obtain this:"
      );
    )
  ) (fun () ->
    List.iter (fun { past; future; goal; _ } ->
      tr (fun () ->
        td "past" (fun () ->
          List.iter (fun (symbol, pos1, pos2) ->
            div (between pos1 pos2) "#90EE90" (fun () ->
              escape_string (print_symbol symbol);
              escape_char ' '
            )
          ) past
        );
        td "future" (fun () ->
          List.iter (fun symbol ->
            escape_string (print_symbol symbol);
            escape_char ' '
          ) future
        );
        td "goal" (fun () ->
          escape_string (print_symbol goal)
        )
      )
    ) explanations
  )

let run print_symbol filename explanations output_filename =
  let script = "\
    function chbg (target, color) { \n\
      document.getElementById(target).style.backgroundColor = color;\n\
    }\n\
  " in
  let style = "\
    pre { background-color: #f0f0f0 }\n\
    table { display: block; overflow-y: scroll; table-layout: fixed; width: 100%; height: 640px; border-spacing: 50px 10px; }\n\
    .past { width: 40%; text-align: right; background-color: #fff0ff; }\n\
    .future { width: 40%; text-align: left; background-color: #f0ffff; }\n\
    .goal { width: 20%; text-align: left; background-color: #fffff0; }\n\
  " in
  Buffer.clear b;
  document_header "Syntax error" style script;
  run print_symbol filename explanations;
  document_footer();
  let c = open_out output_filename in
  output_string c (Buffer.contents b);
  close_out c;
  Buffer.clear b

