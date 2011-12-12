open Types
open Pprint

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
   at indentation 2, and breaks another line. *)
let jump body =
  group (nest 2 (line ^^ body) ^^ line)

(* [definition head body cont] prints [head]; prints [body], surrounded
   with spaces and, if necessary, indented by 2; prints the keyword [in];
   breaks a line, if necessary; and prints [cont]. *)
let definition head body cont =
  group (
    group head ^^ jump body ^^ text "in"
  ) ^^ line ^^
  cont

(*   [join sep (s1 :: s2 :: ... :: sn)]
 * returns
 *   [s1 ^^ sep ^^ s2 ^^ ... ^^ sep ^^ sn] *)
let join sep strings =
  match strings with
  | hd :: tl ->
      List.fold_left (fun sofar s -> sofar ^^ sep ^^ s) hd tl
  | [] ->
      empty

let join_left sep strings =
  List.fold_left (fun sofar s -> sofar ^^ sep ^^ s) empty strings

let print_var var =
  string (Variable.print var)

let print_env env =
  (* First, find out how many toplevel data types are defined in the current
   * environment. *)
  let n_cons = IndexMap.cardinal env.data_type_map in
  (* This small helper function registers all global indexes with their names in
   * the name map. *)
  let rec bind_names i names =
    if i = n_cons then
      names
    else
      let name, _, _ = IndexMap.find i env.data_type_map in
      let name = Variable.print name in
      bind_names (i + 1) (IndexMap.add i name names)
  in
  let names = bind_names 0 IndexMap.empty in
  (* Then, for each of the data types, bind all its parameters to names, and
   * pretty-print it! *)
  let rec print_decl i =
    let name, kind, branches = IndexMap.find i env.data_type_map in
    (* This small helper function recursively inspects the kind, and if the kind
     * is κ₁ → κ₂, then it adds an extra binding for the parameter with kind κ₁
     * and picks a letter for it. We pass a char code, and we start with letter
     * a. The accumulator is here to return a list of all the names we picked
     * for pretty-printing them later on. *)
    let rec bind_names index letter names acc =
      let open SurfaceSyntax in
      function
      | KTerm | KPerm ->
          (* The remaining kind after we've popped all the arguments has to be
           * KType, because data types are kinded as KType. *)
          assert false
      | KType ->
          names, acc
      | KArrow (_k1, k2) ->
          let str = String.make 1 (Char.chr letter) in
          let names = IndexMap.add index str names in
          bind_names (index + 1) (letter + 1) names (str :: acc) k2
    in
    let names, acc = bind_names n_cons (Char.code 'a') names [] kind in
    let params = List.rev_map string acc in
    (string "data") ^^ space ^^ (print_var name) ^^ (join_left space params) ^^
    space ^^ equals ^^ empty
  in
  let decls = List.map print_decl (Hml_List.make n_cons (fun x -> x)) in
  join hardline decls

let string_of_env e =
  let buf = Buffer.create 16 in
  let doc = (print_env e) ^^ hardline in
  Pprint.PpBuffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
