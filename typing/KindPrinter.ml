(* These printers are used purely for debugging purposes. *)

open MzPprint
open Kind
open TypeCore
open Types
open TypePrinter

(* Prints an abstract data type. Very straightforward. *)
let print_abstract_type_def print_env name kind =
  string "abstract" ^^ space ^^ print_var print_env name ^^ space ^^ colon ^^ space ^^
  print_kind kind
;;

let print_variance = function
  | Invariant ->
      empty
  | Covariant ->
      plus
  | Contravariant ->
      minus
  | Bivariant ->
      equals
;;

(* Prints a data type defined in the global scope. Assumes [print_env] has been
   properly populated. *)
let print_data_type_def (env: env) name kind variance branches =
  let params, _return_kind = Kind.as_arrow kind in
  (* Turn the list of parameters into letters *)
  let letters: string list = name_gen (List.length params) in
  let letters = List.map2 (fun variance letter ->
    print_variance variance ^^ utf8string letter
  ) variance letters in
  let env, _, branches =
    bind_datacon_parameters env kind branches
  in
  let sep = break 1 ^^ bar ^^ space in
  (* The whole blurb *)
  string "data" ^^ space ^^ lparen ^^
  print_var env name ^^ space ^^ colon ^^ space ^^
  print_kind kind ^^ rparen ^^ concat_map (precede space) letters ^^
  space ^^ equals ^^
  jump
    (ifflat empty (bar ^^ space) ^^
    separate_map sep (print_unresolved_branch env) branches
    )
;;

let print_abbrev_type_def (env: env) name kind variance t =
  let env, points = make_datacon_letters env kind false in
  let letters = List.map (fun p -> get_name env p) points in
  let letters = List.map2 (fun variance letter ->
    print_variance variance ^^ print_var env letter
  ) variance letters in
  let vars = List.map (fun x -> TyOpen x) points in
  let t = instantiate_type t vars in
  (* The whole blurb *)
  string "alias" ^^ space ^^ lparen ^^
  print_var env name ^^ space ^^ colon ^^ space ^^
  print_kind kind ^^ rparen ^^ concat_map (precede space) letters ^^
  space ^^ equals ^^ space ^^ print_type env t
;;

let print_def env name kind variance def =
  match def with
  | Concrete branches ->
      print_data_type_def env name kind variance branches
  | Abbrev t ->
      print_abbrev_type_def env name kind variance t
  | Abstract ->
      print_abstract_type_def env name kind
;;

(* This function prints the contents of a [Types.env]. *)
let print_kinds env =
  (* Now we have a pretty-printing environment that's ready, proceed. *)
  let defs = fold_definitions env (fun acc var definition ->
    let name = get_name env var in
    let kind = get_kind env var in
    let variance = get_variance env var in
    print_def env name kind variance definition :: acc
  ) [] in
  separate (twice (break 1)) defs
;;

let print_group env (group: data_type_group) =
  let defs = List.map (fun data_type ->
    let name = User (module_name env, data_type.data_name) in
    print_def env name data_type.data_kind data_type.data_variance data_type.data_definition
  ) group.group_items in
  nest 2 (separate (twice (break 1)) defs) ^^ hardline
;;


let pgroup buf arg =
  pdoc buf ((fun (env, group) -> print_group env group), arg)
;;


let print_kinds_and_facts program_env =
  colors.red ^^ string "KINDS:" ^^ colors.default ^^
  nest 2 (hardline ^^ print_kinds program_env) ^^ hardline ^^
  hardline ^^
  colors.red ^^ string "FACTS:" ^^ colors.default ^^
  nest 2 (hardline ^^ print_facts program_env) ^^ hardline
;;

