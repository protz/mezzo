(* This module defines the syntax of types, as manipulated by the
   type-checker. *)

(* In the surface syntax, variables are named. Here, variables are
   represented as de Bruijn indices. We keep a variable name at each
   binding site as a pretty-printing hint. *)

type index =
  int

type level =
  int

type kind =
  SurfaceSyntax.kind

let flatten_kind =
  SurfaceSyntax.flatten_kind

module IndexMap = Hml_Map.Make(struct
  type t = index
  let compare = Pervasives.compare
end)

module LevelMap = IndexMap

type type_binding =
    SurfaceSyntax.type_binding

module DataconMap = Hml_Map.Make(struct
  type t = Datacon.name
  let compare = Pervasives.compare
end)

(* Record fields remain named. *)

module Field = Variable

(* The annotations [Consumes] and [ConsumesAndProduces] that appear in the
   surface syntax are desugared. They do not appear at this level. *)

(* In the surface syntax, tuple types can bind names for their components.
   Here, this is desugared using singleton types, universal quantification,
   and existential quantification. Tuple type components are now anonymous. *)

(* TEMPORARY we need a notion of type equality, or subtyping, that deals with
   quantifiers in a transparent way -- especially the quantifiers introduced
   by the translation of named tuple components down to this kernel syntax.
   E.g. we need (the translation of) [t] to be interconvertible with (the
   translation of) [(x: t)], which is [exists x :: term. (=x, permission x: t)].
   Hmm, tricky, tricky. Do we really want to go this way? *)

(* TEMPORARY also, subtyping must take into account the AC axioms for TyStar,
   the fact that TyEmpty is neutral for TyStar, and (perhaps) the fact that
   duplicable permissions are idempotent for TyStar. Tricky, tricky. *)

(* TEMPORARY also, subtyping must take into account the fact that tuple
   components which are anonymous permissions can freely move around
   within a tuple. Hmm, hmm. *)

(* TEMPORARY perhaps we could completely avoid the need for subtyping
   (and solve all three problems above) by working with explicit
   eta-expansions instead. This requires thought! *)

type typ =
    (* Special type constants. *)
  | TyUnknown
  | TyDynamic

    (* Flexible type variables. *)
  | TyFlexible of PersistentUnionFind.point

    (* Type variables and quantification. Type application. *)
  | TyVar of index
  | TyForall of type_binding * typ
  | TyExists of type_binding * typ
  | TyApp of typ * typ

    (* Structural types. *)
  | TyTuple of tuple_type_component list
  | TyConcreteUnfolded of data_type_def_branch

    (* Singleton types. *)
  | TySingleton of typ

    (* Function types. *)
  | TyArrow of typ * typ

    (* Permissions. *)
  | TyAnchoredPermission of typ * typ
  | TyEmpty
  | TyStar of typ * typ
  (* TEMPORARY perhaps TyEmpty and TyStar can be removed because we already
               have TyTuple, which could serve to construct tuples of
               permissions. Investigate. *)

and tuple_type_component =
  | TyTupleComponentValue of typ
  | TyTupleComponentPermission of typ

and data_type_def_branch =
    Datacon.name * data_field_def list

and data_field_def =
  | FieldValue of (Field.name * typ)
  | FieldPermission of typ

and data_type_entry =
  | Concrete of SurfaceSyntax.data_type_flag * Variable.name * kind * data_type_def_branch list
  | Abstract of Variable.name * kind

(* ---------------------------------------------------------------------------- *)

(* Program-wide environment. *)

(* A fact refers to a data type, and is obtained after running an analysis on
 * the data type definition. A type can be either, affine, or duplicable. The
 * bitmap indicates which levels have to be duplicable for the type itself to be
 * duplicable; it is affine otherwise. *)
type fact = Exclusive | Duplicable of bitmap | Affine

(* This maps levels of the current type parameters to () if that index has to be
 * duplicable, nothing otherwise. *)
and bitmap = unit LevelMap.t

(** Currently, there's only one such environment per file. It's created after we
 * analyzed all type definitions, their well-kindedness, and inferred the facts
 * related to them. It is created once, and doesn't change afterwards.
 * Everything in there has levels as keys. *)
type program_env = {
  type_for_datacon: level DataconMap.t;
  fact_for_type: fact LevelMap.t;
  def_for_type: data_type_entry LevelMap.t;
}

(* Various helper functions. *)

let fact_for_type (program_env: program_env) (level: level): fact =
  match LevelMap.find_opt level program_env.fact_for_type with
  | Some fact ->
      fact
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let total_number_of_data_types (program_env: program_env): int =
  LevelMap.cardinal program_env.def_for_type
;;

let branches_for_type (program_env: program_env) (level: level): data_type_def_branch list =
  match LevelMap.find_opt level program_env.def_for_type with
  | Some (Concrete (_, _name, _kind, branches)) ->
      branches 
  | Some (Abstract (name, _)) ->
      Log.error "No branches for type %a, it is abstract" Variable.p name
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let kind_for_type (program_env: program_env) (level: level): kind =
  match LevelMap.find_opt level program_env.def_for_type with
  | Some (Concrete (_, _name, kind, _) | Abstract (_name, kind)) ->
      kind
  | None ->
      Log.error "There is no type defined at level %d" level
;;

let type_for_datacon (program_env: program_env) (datacon: Datacon.name): level =
  match DataconMap.find_opt datacon program_env.type_for_datacon with
  | Some level ->
      level
  | None ->
      Log.error "There is no type for constructor %a" Datacon.p datacon
;;

let arity_for_data_type (program_env: program_env) (l: level): int =
  let _, tl = flatten_kind (kind_for_type program_env l) in
  List.length tl
;;

(* TODO: we should flatten type applications as soon as we can... *)
let flatten_tyapp t =
  let rec flatten_tyapp acc = function
    | TyApp (t1, t2) ->
        flatten_tyapp (t2 :: acc) t1
    | _ as x ->
        x, acc
  in
  flatten_tyapp [] t
;;

(* ---------------------------------------------------------------------------- *)

(* Fun with de Bruijn indices. *)

(* ---------------------------------------------------------------------------- *)

(* Printers. *)

module TypePrinter = struct

  open Hml_Pprint

  (* --------------------------------------------------------------------------- *)

  (** This is an internal type that is used for pretty-printing. It's not related
   * to the env type defined in [Types]. *)
  type print_env = {
    names: string LevelMap.t;
    level: level;
  }

  (** Aad a name ([string]) to the [print_env] and bump the index. *)
  let add str { names; level } =
    { level = level + 1; names = LevelMap.add level str names }
  ;;

  (** Aad a name ([Variable.name]) to the [print_env] and bump the index. *)
  let add_var var print_env =
    add (Variable.print var) print_env
  ;;

  let print_var var =
    print_string (Variable.print var)
  ;;

  let print_datacon datacon =
    print_string (Datacon.print datacon)
  ;;

  let print_field field =
    print_string (Field.print field)
  ;;

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
  ;;

  (* This is for debugging purposes. Use with [Log.debug] and [%a]. *)
  let p_kind buf kind =
    Pprint.PpBuffer.pretty 1.0 80 buf (print_kind kind)
  ;;

  let print_index { names; level } i =
    let name = LevelMap.find (level - i) names in
    print_string name
  ;;

  let rec print_quantified
      (print_env: print_env)
      (q: string)
      (name: Variable.name) 
      (kind: SurfaceSyntax.kind)
      (typ: typ) =
    print_string q ^^ lparen ^^ print_var name ^^ space ^^ ccolon ^^ space ^^
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

    | TyFlexible _ ->
        string "[flexible]"

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
  ;;

  (* Prints a sequence of characters representing whether each parameter has to
   * be duplicable (x) or not (nothing). *)
  let print_fact (program_env, l: program_env * level): document =
    let n = total_number_of_data_types program_env in
    let arity = arity_for_data_type program_env l in
    match fact_for_type program_env l with
    | Duplicable bitmap ->
        join empty (Hml_List.make arity (fun l ->
          match IndexMap.find_opt (n + l) bitmap with
          | Some () -> string "x"
          | None -> string "-")
        )
    | Exclusive ->
        string "exclusive"
    | Affine ->
        string "affine"
  ;;

  let print_facts (program_env: program_env): document =
    let is name ?params w =
      let params =
        match params with
        | Some params -> join_left space (List.map print_string params)
        | None -> empty
      in
      colors.underline ^^ print_var name ^^ params ^^
      colors.default ^^ string " is " ^^ print_string w
    in
    let n = total_number_of_data_types program_env in
    let print_fact name arity fact =
      let params = Hml_Pprint.name_gen arity in
      let is w = is name ~params w in
      match fact with
      | Exclusive ->
          is "exclusive"
      | Affine ->
          is "affine"
      | Duplicable bitmap when LevelMap.cardinal bitmap = 0 ->
          is "duplicable"
      | Duplicable bitmap ->
          let dup_params = Hml_List.mapi (fun i param ->
            match LevelMap.find_opt (n + i) bitmap with
            | Some () ->
                Some param
            | None ->
                None
          ) params in
          let dup_params = Hml_List.filter_some dup_params in
          let verb = string (if List.length dup_params > 1 then " are " else " is ") in
          let dup_params = List.map print_string dup_params in
          is "duplicable if " ^^ english_join dup_params ^^ verb ^^
          string "duplicable"
    in
    let lines =
      Hml_List.make n (fun level ->
        match LevelMap.find level program_env.def_for_type with
        | Concrete (_flag, name, kind, _branches) ->
            let fact = fact_for_type program_env level in
            let arity = arity_for_data_type program_env level in
            print_fact name arity fact
        | Abstract (name, _kind) ->
            is name "abstract"
      )
    in
    join hardline lines
  ;;


end
