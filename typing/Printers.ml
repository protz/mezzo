open Types
open Pprint

module MyPprint = struct
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
end

open MyPprint

(* --------------------------------------------------------------------------- *)

(** This is an internal type that is used for pretty-printing. It's not related
 * to the env type defined in [Types]. *)
type print_env = {
  names: string IndexMap.t;
  index: int;
}

let add str { names; index } =
  Log.debug "Adding %s at %d" str index;
  { index = index + 1; names = IndexMap.add index str names }

let add_var var print_env =
  add (Variable.print var) print_env

(* --------------------------------------------------------------------------- *)

let arrow = (string "->")

let print_var var =
  string (Variable.print var)

let print_datacon datacon =
  string (Datacon.print datacon)

let print_field field =
  string (Field.print field)

let print_kind =
  let open SurfaceSyntax in
  function
  | KTerm ->
      string "term"
  | KPerm ->
      string "perm"
  | KType ->
      string "*"
  | _ ->
      assert false

let print_index { names; _ } index =
  string (IndexMap.find index names)

let rec print_quantified
    (print_env: print_env)
    (q: string)
    (name: Variable.name) 
    (kind: SurfaceSyntax.kind)
    (typ: typ) =
  (fancystring q 1) ^^ lparen ^^ (print_var name) ^^ colon ^^ colon ^^
  (print_kind kind) ^^ rparen ^^ dot ^^ space ^^ (print_type print_env typ)

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
      (print_type print_env t1) ^^ space ^^ (print_type print_env t2)

  | TyTuple components ->
      lparen ^^ (join (comma ^^ space)
        (List.map (print_tuple_type_component print_env) components)) ^^
      rparen

  | TyConcreteUnfolded branch ->
      print_data_type_def_branch print_env branch

    (* Singleton types. *)
  | TySingleton typ ->
      equals ^^ print_type print_env typ

    (* Function types. *)
  | TyArrow (t1, t2) ->
      (print_type print_env t1) ^^ arrow ^^ (print_type print_env t2)

    (* Permissions. *)
  | TyAnchoredPermission (t1, t2) ->
      (print_type print_env t1) ^^ colon ^^ space ^^ (print_type print_env t2)
  | TyEmpty ->
      (string "empty")
  | TyStar (t1, t2) ->
      (print_type print_env t1) ^^ star ^^ (print_type print_env t2)

and print_tuple_type_component print_env = function
  | TyTupleComponentValue typ ->
      print_type print_env typ

  | TyTupleComponentPermission typ ->
      (string "permission") ^^ space ^^ (print_type print_env typ)

and print_data_field_def print_env = function
  | FieldValue (name, typ) ->
      (print_field name) ^^ colon ^^ space ^^ (print_type print_env typ)
  | FieldPermission typ ->
      (string "permission") ^^ space ^^ (print_type print_env typ)

and print_data_type_def_branch print_env (branch: data_type_def_branch) =
  let name, fields = branch in
  let record =
    if List.length fields > 0 then
      space ^^ lbrace ^^
      nest 2 (break1 ^^ (join break1 (List.map (print_data_field_def print_env) fields))) ^^
      break1 ^^ rbrace
    else empty
  in
  bar ^^ space ^^ (print_datacon name) ^^ record

let p_var buf var =
  Buffer.add_string buf (Variable.print var)

(** This function prints the contents of a [Types.env]. *)
let print_env env =
  (* Create an empty printing environment *)
  let print_env = { index = 0; names = IndexMap.empty; } in
  (* First, find out how many toplevel data types are defined in the current
   * environment. *)
  let n_cons = IndexMap.cardinal env.data_type_map in
  Log.debug "%d bindings found" n_cons;
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
  Log.debug "Index is now at %d" print_env.index;
  let print_env = bind_datacon_names print_env in
  Log.debug "Index is now at %d" print_env.index;
  (* Then, for each of the data types, bind all its parameters to names, and
   * pretty-print it! *)
  let rec print_decl i =
    let name, kind, branches = IndexMap.find i env.data_type_map in
    Log.debug "Entering %a at %d" p_var name i;
    (* This small helper function recursively inspects the kind, and if the kind
     * is κ₁ → κ₂, then it adds an extra binding for the parameter with kind κ₁
     * and picks a letter for it. We pass a char code, and we start with letter
     * a. The accumulator is here to return a list of all the names we picked
     * for pretty-printing them later on. *)
    let rec bind_param_names print_env letter acc =
      let open SurfaceSyntax in
      function
      | KTerm | KPerm ->
          (* The remaining kind after we've popped all the arguments has to be
           * KType, because data types are kinded as KType. *)
          assert false
      | KType ->
          print_env, acc
      | KArrow (k1, k2) ->
          let str = String.make 1 (Char.chr letter) in
          let print_env = add str print_env in
          bind_param_names print_env (letter + 1) ((str, k1) :: acc) k2
    in
    let print_env, acc = bind_param_names print_env (Char.code 'a') [] kind in
    let params = List.rev_map
      (fun (var, k) ->
        lparen ^^ (string var) ^^ colon ^^ colon ^^ space ^^ (print_kind k) ^^ rparen)
      acc
    in
    (string "data") ^^ space ^^ (print_var name) ^^ (join_left space params) ^^
    space ^^ equals ^^
    (nest 2
      (break1 ^^ join break1 (List.map (print_data_type_def_branch print_env) branches)))
  in
  let decls = List.map print_decl (Hml_List.make n_cons (fun x -> x)) in
  join (hardline ^^ hardline) decls

(** This function takes a [Types.env] and returns a string representation of it
 * suitable for debugging / pretty-printing. *)
let string_of_env e =
  let buf = Buffer.create 16 in
  let doc = (print_env e) ^^ hardline in
  Pprint.PpBuffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
