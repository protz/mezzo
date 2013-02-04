(* Copied from OCaml's lexer.mll, version 4.00.0 *)

let create_hashtable n elements =
  let table = Hashtbl.create n in
  List.iter (fun element ->
    Hashtbl.add table element ()
  ) elements;
  table

let keyword_table =
  create_hashtable 149 [
    "and";
    "as";
    "assert";
    "begin";
    "class";
    "constraint";
    "do";
    "done";
    "downto";
    "else";
    "end";
    "exception";
    "external";
    "false";
    "for";
    "fun";
    "function";
    "functor";
    "if";
    "in";
    "include";
    "inherit";
    "initializer";
    "lazy";
    "let";
    "match";
    "method";
    "module";
    "mutable";
    "new";
    "object";
    "of";
    "open";
    "or";
(*  "parser"; *)
    "private";
    "rec";
    "sig";
    "struct";
    "then";
    "to";
    "true";
    "try";
    "type";
    "val";
    "virtual";
    "when";
    "while";
    "with";

    "mod";
    "land";
    "lor";
    "lxor";
    "lsl";
    "lsr";
    "asr";
]
