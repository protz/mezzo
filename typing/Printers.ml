(** This modules provides various printers. *)

open Types
open Pprint

(* This module contains extra helper functions for [Pprint]. *)

module MyPprint = struct
  let arrow = string "->"

  let ccolon = colon ^^ colon

  let int i = string (string_of_int i)

  (* [heading head body] prints [head]; breaks a line and indents by 2,
   if necessary; then prints [body]. *)
  let heading head body =
    group (
      nest 2 (
        group head ^^ linebreak ^^
        body
      )
    )

  (* [jump body] either displays a space, followed with [body], followed
     with a space, all on a single line; or breaks a line, prints [body]
     at indentation 2. *)
  let jump body =
    group (nest 2 (line ^^ body))

  (* [definition head body cont] prints [head]; prints [body], surrounded
     with spaces and, if necessary, indented by 2; prints the keyword [in];
     breaks a line, if necessary; and prints [cont]. *)
  let definition head body cont =
    group (
      group head ^^ jump body ^^ text "in"
    ) ^^ line ^^
    cont

  (* [join sep (s1 :: s2 :: ... :: sn)] returns
   * [s1 ^^ sep ^^ s2 ^^ ... ^^ sep ^^ sn] *)
  let join sep strings =
    match strings with
    | hd :: tl ->
        List.fold_left (fun sofar s -> sofar ^^ sep ^^ s) hd tl
    | [] ->
        empty

  (* [join_left sep (s1 :: s2 :: ... :: sn)] returns
   * [sep ^^ s1 ^^ sep ^^ s2 ^^ ... ^^ sep ^^ sn] *)
  let join_left sep strings =
    List.fold_left (fun sofar s -> sofar ^^ sep ^^ s) empty strings
end

open MyPprint

(* --------------------------------------------------------------------------- *)

(** This is an internal type that is used for pretty-printing. It's not related
 * to the env type defined in [Types]. *)
type print_env = {
  names: string IndexMap.t;
  index: int;
}

(** Aad a name ([string]) to the [print_env] and bump the index. *)
let add str { names; index } =
  { index = index + 1; names = IndexMap.add index str names }

(** Aad a name ([Variable.name]) to the [print_env] and bump the index. *)
let add_var var print_env =
  add (Variable.print var) print_env

(* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
let p_con buf con =
  Buffer.add_string buf (Datacon.print con)

(* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
let p_var buf var =
  Buffer.add_string buf (Variable.print var)

(* Transforms [κ₁ → ... → κₙ → κ₀] in [[κ₁; ...; κₙ], κ₀] *)
let flatten_kind kind =
  let open SurfaceSyntax in
  let rec flatten_kind acc = function
    | KArrow (k1, k2) ->
        flatten_kind (k1 :: acc) k2
    | _ as k ->
        acc, k
  in
  let acc, k = flatten_kind [] kind in
  List.rev acc, k

(* --------------------------------------------------------------------------- *)

let print_var var =
  string (Variable.print var)

let print_datacon datacon =
  string (Datacon.print datacon)

let print_field field =
  string (Field.print field)

let rec print_kind =
  let open SurfaceSyntax in
  function
  | KTerm ->
      string "term"
  | KPerm ->
      string "perm"
  | KType ->
      string "∗"
  | KArrow (k1, k2) ->
      print_kind k1 ^^ space ^^ arrow ^^ space ^^ print_kind k2

let print_index { names; index } i =
  let name = IndexMap.find (index - i) names in
  string name

let rec print_quantified
    (print_env: print_env)
    (q: string)
    (name: Variable.name) 
    (kind: SurfaceSyntax.kind)
    (typ: typ) =
  fancystring q 1 ^^ lparen ^^ print_var name ^^ space ^^ ccolon ^^ space ^^
  print_kind kind ^^ rparen ^^ dot ^^ jump (print_type print_env typ)

(* TEMPORARY this does not respect precedence and won't insert parentheses at
 * all! *)
and print_type print_env = function
  | TyUnknown ->
      string "unknown"

  | TyDynamic ->
      string "dynamic"

  | TyVar index ->
      print_index print_env index

  | TyForall ((name, kind), typ) ->
      let print_env = add_var name print_env in
      print_quantified print_env "∀" name kind typ

  | TyExists ((name, kind), typ) ->
      let print_env = add_var name print_env in
      print_quantified print_env "∃" name kind typ

  | TyApp (t1, t2) ->
      print_type print_env t1 ^^ space ^^ print_type print_env t2

  | TyTuple components ->
      lparen ^^
      join
        (comma ^^ space)
        (List.map (print_tuple_type_component print_env) components) ^^
      rparen

  | TyConcreteUnfolded branch ->
      print_data_type_def_branch print_env branch

    (* Singleton types. *)
  | TySingleton typ ->
      equals ^^ print_type print_env typ

    (* Function types. *)
  | TyArrow (t1, t2) ->
      print_type print_env t1 ^^ space ^^ arrow ^^
      group (break1 ^^ print_type print_env t2)

    (* Permissions. *)
  | TyAnchoredPermission (t1, t2) ->
      print_type print_env t1 ^^ colon ^^ space ^^ print_type print_env t2

  | TyEmpty ->
      string "empty"

  | TyStar (t1, t2) ->
      print_type print_env t1 ^^ star ^^ print_type print_env t2

and print_tuple_type_component print_env = function
  | TyTupleComponentValue typ ->
      print_type print_env typ

  | TyTupleComponentPermission typ ->
      string "permission" ^^ space ^^ print_type print_env typ

and print_data_field_def print_env = function
  | FieldValue (name, typ) ->
      print_field name ^^ colon ^^ jump (print_type print_env typ)

  | FieldPermission typ ->
      string "permission" ^^ space ^^ print_type print_env typ

and print_data_type_def_branch print_env (branch: data_type_def_branch) =
  let name, fields = branch in
  let record =
    if List.length fields > 0 then
      space ^^ lbrace ^^
      nest 4
        (break1 ^^ join
          (semi ^^ break1)
          (List.map (print_data_field_def print_env) fields)) ^^
      nest 2 (break1 ^^ rbrace)
    else
      empty
  in
  print_datacon name ^^ record

(* Prints a data type defined in the global scope. Assumes [print_env] has been
   properly populated. *)
let print_data_type_def print_env name kind branches =
  let params, _return_kind = flatten_kind kind in
  (* Turn the list of parameters into letters *)
  let params: string list =
    (* Of course, won't work nice if more than 26 type parameters... *)
    let a = Char.code 'a' in
    Hml_List.mapi (fun i acc ->
      let code = a + i in
      String.make 1 (Char.chr code)
    ) params
  in
  (* Add all these letters into the printing environment *)
  let print_env = List.fold_left (fun print_env param ->
    add param print_env) print_env params
  in
  (* Make these printable now *)
  let params = List.map string params in
  let sep = break1 ^^ bar ^^ space in
  (* The whole blurb *)
  string "data" ^^ space ^^ lparen ^^
  print_var name ^^ space ^^ ccolon ^^ space ^^
  print_kind kind ^^ rparen ^^ join_left space params ^^
  space ^^ equals ^^
  jump
    ((ifflat empty (bar ^^ space)) ^^
    join sep (List.map (print_data_type_def_branch print_env) branches))

(* This function prints the contents of a [Types.env]. *)
let print_env env =
  (* Create an empty printing environment *)
  let print_env = { index = 0; names = IndexMap.empty; } in
  (* First, find out how many toplevel data types are defined in the current
   * environment. *)
  let n_cons = IndexMap.cardinal env.data_type_map in
  (* This small helper function registers all global indexes with their names in
   * the name map. *)
  let rec bind_datacon_names print_env =
    let { index; names } = print_env in
    if index = n_cons then
      print_env
    else
      let name, _, _ = IndexMap.find index env.data_type_map in
      bind_datacon_names (add_var name print_env)
  in
  let print_env = bind_datacon_names print_env in
  (* Now we have a pretty-printing environment that's ready, proceed. *)
  let defs = Hml_List.make n_cons (fun i ->
    let name, kind, branches = IndexMap.find i env.data_type_map in
    print_data_type_def print_env name kind branches)
  in
  join (break1 ^^ break1) defs

(* This function takes a [Types.env] and returns a string representation of it
   suitable for debugging / pretty-printing. *)
let string_of_env e =
  let buf = Buffer.create 16 in
  let doc = (print_env e) in
  Pprint.PpBuffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
