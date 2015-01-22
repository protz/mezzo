(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

open Lexer
open Types

(* -------------------------------------------------------------------------- *)

let chop_mz_or_mzi f =
  if Filename.check_suffix f ".mz" then
    Filename.chop_suffix f ".mz"
  else if Filename.check_suffix f ".mzi" then
    Filename.chop_suffix f ".mzi"
  else
    invalid_arg "chop_mz_or_mzi"
;;

(* [print_symbol] *)

module PS = struct

  open Grammar.MenhirInterpreter

  (* Painful. Plus, should update this list when the list of keywords
     changes. TEMPORARY auto-generate the part that concerns keywords *)

  let print_symbol symbol =
    match symbol with
    | X (T T_error) -> "error"
    | X (T T_WITNESS) -> "witness"
    | X (T T_WITH) -> "with"
    | X (T T_WHILE) -> "while"
    | X (T T_VALUE) -> "value"
    | X (T T_VAL) -> "val"
    | X (T T_UNKNOWN) -> "unknown"
    | X (T T_UNDERSCORE) -> "_"
    | X (T T_UIDENT) -> "<Data constructor>"
    | X (T T_TYPE) -> "type"
    | X (T T_TO) -> "to"
    | X (T T_THEN) -> "then"
    | X (T T_TAKING) -> "taking"
    | X (T T_TAKE) -> "take"
    | X (T T_TAGOF) -> "tag of"
    | X (T T_STAR) -> "*"
    | X (T T_SEMI) -> ";"
    | X (T T_RPAREN) -> ")"
    | X (T T_REC) -> "rec"
    | X (T T_RBRACKET) -> "]"
    | X (T T_RBRACE) -> "}"
    | X (T T_PRESERVING) -> "preserving"
    | X (T T_PLUS) -> "+"
    | X (T T_PERM) -> "perm"
    | X (T T_PACK) -> "pack"
    | X (T T_OPPREFIX) -> "!"   (* a representative choice *)
    | X (T T_OPINFIX4) -> "**"
    | X (T T_OPINFIX3) -> "***" (* a representative choice *)
    | X (T T_OPINFIX2) -> "++"  (* a representative choice *)
    | X (T T_OPINFIX1) -> "@@"  (* a representative choice *)
    | X (T T_OPINFIX0d) -> "$"
    | X (T T_OPINFIX0c) -> "==" (* a representative choice *)
    | X (T T_OPINFIX0b) -> "&&" (* a representative choice *)
    | X (T T_OPINFIX0a) -> "||" (* a representative choice *)
    | X (T T_OPEN) -> "open"
    | X (T T_MUTABLE) -> "mutable"
    | X (T T_MINUS) -> "-"
    | X (T T_MATCH) -> "match"
    | X (T T_LPAREN) -> "("
    | X (T T_LIDENT) -> "<identifier>"
    | X (T T_LET) -> "let"
    | X (T T_LBRACKET) -> "["
    | X (T T_LBRACE) -> "{"
    | X (T T_LARROW) -> "<-"
    | X (T T_INT) -> "42" (* a representative choice *)
    | X (T T_IN) -> "in"
    | X (T T_IF) -> "if"
    | X (T T_GIVE) -> "give"
    | X (T T_FUN) -> "fun"
    | X (T T_FROM) -> "from"
    | X (T T_FOR) -> "for"
    | X (T T_FLEX) -> "flex"
    | X (T T_FAIL) -> "fail"
    | X (T T_FACT) -> "fact"
    | X (T T_EXPLAIN) -> "explain"
    | X (T T_EXCLUSIVE) -> "exclusive"
    | X (T T_EQUAL) -> "="
    | X (T T_EOF) -> "<eof>"
    | X (T T_END) -> "end"
    | X (T T_EMPTY) -> "empty"
    | X (T T_ELSE) -> "else"
    | X (T T_DYNAMIC) -> "dynamic"
    | X (T T_DUPLICABLE) -> "duplicable"
    | X (T T_DOWNTO) -> "downto"
    | X (T T_DOT) -> "."
    | X (T T_DO) -> "do"
    | X (T T_DBLARROW) -> "=>"
    | X (T T_DATA) -> "data"
    | X (T T_CONSUMES) -> "consumes"
    | X (T T_COMMA) -> ","
    | X (T T_COLONEQUAL) -> ":="
    | X (T T_COLONCOLON) -> "::"
    | X (T T_COLON) -> ":"
    | X (T T_BUILTIN) -> "builtin"
    | X (T T_BELOW) -> "below"
    | X (T T_BEGIN) -> "begin"
    | X (T T_BAR) -> "|"
    | X (T T_AT) -> "@"
    | X (T T_ASSERT) -> "assert"
    | X (T T_AS) -> "as"
    | X (T T_ARROW) -> "->"
    | X (T T_AND) -> "and"
    | X (T T_ALIAS) -> "alias"
    | X (T T_ADOPTS) -> "adopts"
    | X (T T_ABSTRACT) -> "abstract"
    | X (T T_ABOVE) -> "above"
    | X (N N_warn_error_list) -> assert false
    | X (N N_warn_error) -> assert false
    | X (N N_variance) -> "<variance>"
    | X (N N_variable) -> "<variable>"
    | X (N N_value_declaration) -> "<value declaration>"
    | X (N N_type_parameters) -> "<type parameters>"
    | X (N N_type_binding) -> "<type binding>"
    | X (N N_type_application_component) -> "<type application component>"
    | X (N N_separated_nonempty_list_DBLARROW_mode_constraint_) -> "<mode constraints(1)>"
    | X (N N_separated_nonempty_list_COMMA_variable_) -> "<variables(1)>"
    | X (N N_separated_nonempty_list_COMMA_type_application_component_) -> "<type application components(1)>"
    | X (N N_separated_nonempty_list_COMMA_consumes_type_) -> "<types(consumes/1)>"
    | X (N N_separated_nonempty_list_COMMA_atomic_pattern_) -> "<atomic patterns(1)>"
    | X (N N_separated_nonempty_list_COMMA_algebraic_expression_) -> "<expressions(algebraic/1)>"
    | X (N N_separated_nonempty_list_AND_definition_) -> "<definitions(1)>"
    | X (N N_separated_nonempty_list_AND_concrete_data_type_def_) -> "<data type definitions(1)>"
    | X (N N_right_flexible_list_SEMI_data_field_pattern_) -> "<field patterns>"
    | X (N N_right_flexible_list_SEMI_data_field_expression_) -> "<field expressions>"
    | X (N N_right_flexible_list_SEMI_data_field_def_) -> "<field definitions>"
    | X (N N_right_flexible_list_COMMA_type_binding_) -> "<type bindings>"
    | X (N N_reverse_left_flexible_list_BAR_match_branch_) -> "<branches>"
    | X (N N_reverse_left_flexible_list_BAR_data_type_def_branch_) -> "<data definitions>"
    | X (N N_rec_flag) -> "<rec?>"
    | X (N N_reasonable_expression) -> "<expression(reasonable)>"
    | X (N N_raw_very_loose_type) -> "<type(very loose)>"
    | X (N N_raw_tuple_or_raw_reasonable_expression_) -> "<tuple|expression(reasonable)>"
    | X (N N_raw_tuple_or_raw_fragile_expression_) -> "<tuple|expression(fragile)>"
    | X (N N_raw_tight_type) -> "<type(tight)>"
    | X (N N_raw_tight_expression) -> "<expression(tight)>"
    | X (N N_raw_reasonable_expression) -> "<expression(reasonable)>"
    | X (N N_raw_parenthetic_type) -> "<type(parenthetic)>"
    | X (N N_raw_normal_type_no_adopts) -> "<type(normal)>"
    | X (N N_raw_normal_type) -> "<type(normal)>" (* putting under the rug the distinction with the previous case *)
    | X (N N_raw_normal_pattern) -> "<pattern(normal)>"
    | X (N N_raw_loose_type) -> "<type(loose)>"
    | X (N N_raw_loose_pattern) -> "<pattern(loose)>"
    | X (N N_raw_fragile_expression) -> "<expression(fragile)>"
    | X (N N_raw_fat_type) -> "<type(fat)>"
    | X (N N_raw_consumes_type) -> "<type(consumes)>"
    | X (N N_raw_atomic_type) -> "<type(atomic)>"
    | X (N N_raw_atomic_pattern) -> "<pattern(atomic)>"
    | X (N N_raw_atomic_expression) -> "<expression(atomic)>"
    | X (N N_raw_application_expression) -> "<expression(application)>"
    | X (N N_raw_algebraic_expression) -> "<expression(algebraic)>"
    | X (N N_range) -> assert false
    | X (N N_parenthesized_tuple_components) -> "<expressions(algebraic*.fragile)>"
    | X (N N_optional_preserving) -> "<preserving?>"
    | X (N N_option_preceded_ADOPTS_arbitrary_type__) -> "<adopts clause?>"
    | X (N N_nonempty_list_warn_error_) -> assert false
    | X (N N_mode) -> "<mode>"
    | X (N N_maybe_qualified_variable_) -> "<qualified? variable>"
    | X (N N_maybe_qualified_datacon_) -> "<qualified? data constructor>"
    | X (N N_loption_type_parameters_) -> "<type parameters?>"
    | X (N N_loption_separated_nonempty_list_AND_definition__) -> "<definitions>"
    | X (N N_list_terminated_mode_constraint_DBLARROW__) -> "<mode constraints>" (* putting under the rug the distinction with another symbol *)
    | X (N N_list_interface_item_) -> "<interface items>"
    | X (N N_list_implementation_item_) -> "<implementation items>"
    | X (N N_list_fact_) -> "<facts>"
    | X (N N_list_atomic_type_binding_with_variance_) -> "<atomic type bindings with variance>"
    | X (N N_interface_item) -> "<interface item>"
    | X (N N_interface) -> "<interface>"
    | X (N N_implementation_item) -> "<implementation item>"
    | X (N N_implementation) -> "<implementation>"
    | X (N N_generic_datacon_application_right_flexible_list_SEMI_data_field_pattern__) -> "<data constructor pattern>"
    | X (N N_generic_datacon_application_right_flexible_list_SEMI_data_field_expression__) -> "<data constructor expression>"
    | X (N N_generic_datacon_application_data_type_def_branch_content_) -> "<data constructor definition>"
    | X (N N_flag) -> assert false
    | X (N N_fact) -> "<fact>"
    | X (N N_explain) -> "<explain?>"
    | X (N N_existential_quantifiers) -> "<existential quantifiers>"
    | X (N N_direction) -> "<direction>"
    | X (N N_definition_group) -> "<definition group>"
    | X (N N_definition) -> "<definition>"
    | X (N N_data_type_def_branch_content) -> "<data constructor parameters>" (* not great *)
    | X (N N_data_field_pattern) -> "<field pattern>"
    | X (N N_data_field_expression) -> "<field expression>"
    | X (N N_data_field_def) -> "<field definition>"
    | X (N N_concrete_data_type_def) -> "<data type definition>"
    | X (N N_atomic_type_binding_with_variance) -> "<atomic type binding with variance>"
    | X (N N_atomic_type_binding) -> "<atomic type binding>"
    | X (N N_atomic_kind) -> "<kind>"
    | X (N N_anonymous_function) -> "<function>"
    | X (N N_abstract_data_type_def) -> "<abstract type definition>"
    | X (N N_abbreviation_def) -> "<alias definition>"

end

(* [terminal2token] *)

module TT = struct

  open Grammar
  open Grammar.MenhirInterpreter

  let terminal2token (type a) (t : a terminal) : token =
    match t with
    | T_error ->
        assert false
    | T_WITNESS -> WITNESS
    | T_WITH -> WITH
    | T_WHILE -> WHILE
    | T_VALUE -> VALUE
    | T_VAL -> VAL
    | T_UNKNOWN -> UNKNOWN
    | T_UNDERSCORE -> UNDERSCORE
    | T_UIDENT -> UIDENT ""
    | T_TYPE -> TYPE
    | T_TO -> TO
    | T_THEN -> THEN
    | T_TAKING -> TAKING
    | T_TAKE -> TAKE
    | T_TAGOF -> TAGOF
    | T_STAR -> STAR ""
    | T_SEMI -> SEMI
    | T_RPAREN -> RPAREN
    | T_REC -> REC
    | T_RBRACKET -> RBRACKET
    | T_RBRACE -> RBRACE
    | T_PRESERVING -> PRESERVING
    | T_PLUS -> PLUS ""
    | T_PERM -> PERM
    | T_PACK -> PACK
    | T_OPPREFIX -> OPPREFIX ""
    | T_OPINFIX4 -> OPINFIX4 ""
    | T_OPINFIX3 -> OPINFIX3 ""
    | T_OPINFIX2 -> OPINFIX2 ""
    | T_OPINFIX1 -> OPINFIX1 ""
    | T_OPINFIX0d -> OPINFIX0d ""
    | T_OPINFIX0c -> OPINFIX0c ""
    | T_OPINFIX0b -> OPINFIX0b ""
    | T_OPINFIX0a -> OPINFIX0a ""
    | T_OPEN -> OPEN
    | T_MUTABLE -> MUTABLE
    | T_MINUS -> MINUS ""
    | T_MATCH -> MATCH
    | T_LPAREN -> LPAREN
    | T_LIDENT -> LIDENT ""
    | T_LET -> LET
    | T_LBRACKET -> LBRACKET
    | T_LBRACE -> LBRACE
    | T_LARROW -> LARROW
    | T_INT -> INT 0
    | T_IN -> IN
    | T_IF -> IF
    | T_GIVE -> GIVE
    | T_FUN -> FUN
    | T_FROM -> FROM
    | T_FOR -> FOR
    | T_FLEX -> FLEX
    | T_FAIL -> FAIL
    | T_FACT -> FACT
    | T_EXPLAIN -> EXPLAIN
    | T_EXCLUSIVE -> EXCLUSIVE
    | T_EQUAL -> EQUAL ""
    | T_EOF -> EOF
    | T_END -> END
    | T_EMPTY -> EMPTY
    | T_ELSE -> ELSE
    | T_DYNAMIC -> DYNAMIC
    | T_DUPLICABLE -> DUPLICABLE
    | T_DOWNTO -> DOWNTO
    | T_DOT -> DOT
    | T_DO -> DO
    | T_DBLARROW -> DBLARROW
    | T_DATA -> DATA
    | T_CONSUMES -> CONSUMES
    | T_COMMA -> COMMA
    | T_COLONEQUAL -> COLONEQUAL ""
    | T_COLONCOLON -> COLONCOLON
    | T_COLON -> COLON
    | T_BUILTIN -> BUILTIN
    | T_BELOW -> BELOW
    | T_BEGIN -> BEGIN
    | T_BAR -> BAR
    | T_AT -> AT
    | T_ASSERT -> ASSERT
    | T_AS -> AS
    | T_ARROW -> ARROW
    | T_AND -> AND
    | T_ALIAS -> ALIAS
    | T_ADOPTS -> ADOPTS
    | T_ABSTRACT -> ABSTRACT
    | T_ABOVE -> ABOVE

end

(* Lexing and parsing, built on top of [grammar]. *)

module P =
  MenhirLib.Printers.Make
    (Grammar.MenhirInterpreter)
    (struct
      let print s = Printf.fprintf stderr "%s" s
      let print_symbol s = print (PS.print_symbol s)
      let print_element = None
     end)

module E =
  MenhirLib.ErrorReporting.Make
    (Grammar.MenhirInterpreter)
    (TT)

let lex_and_parse_raw lexbuf file_path (entry : unit -> 'a Grammar.MenhirInterpreter.result) : 'a =
  let the_parser = E.entry (entry()) in
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised the_parser in
  try
    Lexer.init file_path;
    the_parser (fun _ -> Lexer.token lexbuf)
  with
    | Ulexing.Error ->
        Printf.eprintf
          "Lexing error at offset %i\n" (Ulexing.lexeme_end lexbuf);
        exit 255
    | Ulexing.InvalidCodepoint i ->
        Printf.eprintf
          "Invalid code var %i at offset %i\n" i (Ulexing.lexeme_end lexbuf);
        exit 254
    | E.Error (_, explanations) ->
        MzString.beprintf "%a\nError: Syntax error\n"
          print_position lexbuf;
        List.iter (fun e -> P.print_item e.MenhirLib.ErrorReporting.item) explanations;
        HtmlOutput.run PS.print_symbol file_path explanations "report.html";
        let start_pos = Lexer.start_pos lexbuf in
        let end_pos = Lexer.end_pos lexbuf in
        JsGlue.highlight_range start_pos end_pos;
        exit 253
    | Lexer.LexingError e ->
        MzString.beprintf "%a\n"
          Lexer.print_error (lexbuf, e);
        exit 252
    | e ->
      Format.eprintf "Exception during lexing/parsing: %s@." (Printexc.to_string e);
      exit 251

;;

let lex_and_parse file_path entry_var =
  Utils.with_open_in file_path (fun file_desc ->
  let lexbuf = Ulexing.from_utf8_channel file_desc in
  lex_and_parse_raw lexbuf file_path entry_var
  )
;;

(* The [mkprefix] function is called for every interface we depend on + one more
 * time for the actual implementation we're type-checking, so we're trying to
 * avoid doing the same computations every time. *)
let corelib_dirs = lazy begin
  (* So it's the [lib_dir] that we want here, unless we're in the process of
   * pre-compiling the Mezzo core library, meaning that [lib_dir] isn't ready. *)
  if !Options.js then
    "corelib", ""
  else if !Options.boot || Configure.local then
    Filename.concat Configure.src_dir "corelib",
    Filename.concat (Filename.concat Configure.src_dir "_build") "corelib"
  else
    (* ocamlfind requires us to have a flat directory structure, d'oh... *)
    Configure.lib_dir,
    ""
end;;

let autoload_modules = lazy begin
  let corelib_dir, _ = !*corelib_dirs in
  let autoload_path = Filename.concat corelib_dir "autoload" in
  let autoload_modules = MzString.split (Utils.file_get_contents autoload_path) '\n' in
  let autoload_modules = List.filter (fun s -> String.length s > 0 && s.[0] <> '#') autoload_modules in
  autoload_modules
end;;

let mkprefix path =
  if !Options.no_auto_include && path = !Options.filename then
    []
  else
    let corelib_dir, corelib_build_dir = !*corelib_dirs in
    let me = Filename.basename path in
    let my_dir = Filename.dirname path in
    let chop l =
      let rec chop acc = function
        | hd :: tl ->
            if hd ^ ".mz" = me || hd ^ ".mzi" = me then
              List.rev acc
            else
              chop (hd :: acc) tl
        | [] ->
            List.rev acc
      in
      chop [] l
    in
    (* So. In the case of a packaged mezzo, me_in_core_directory will return
     * true even for stdlib modules, because findlib mandates a flat directory
     * structure ($@#!!), however, it's mostly harmless, since [chop] will just
     * run through the whole list without finding a match. *)
    let me_in_core_directory =
      Utils.same_absolute_path corelib_dir my_dir ||
      Utils.same_absolute_path corelib_build_dir my_dir
    in
    Log.debug "In core directory? %b" me_in_core_directory;
    (* If we're processing an .mz file (meaning, the actual .mz file we want to
     * operate on, not an .mzi that we depend on), and we're _not_ in the
     * core directory, and we have the same name as a legit module that's
     * auto-loaded, bail now rather than complain about a cryptic dependency
     * error. *)
    let me_noext = chop_mz_or_mzi me in
    if Filename.check_suffix me ".mz" &&
       not me_in_core_directory &&
       List.exists ((=) me_noext) !*autoload_modules
    then
      TypeErrors.(raise_error TypeCore.empty_env (OverrideAutoload me_noext));
    let modules =
      if me_in_core_directory then
        chop !*autoload_modules
      else
        !*autoload_modules
    in
    List.map (fun x ->
      SurfaceSyntax.OpenDirective (Module.register x)
    ) modules
;;

let lex_and_parse_implementation path : SurfaceSyntax.implementation =
  mkprefix path @ lex_and_parse path Grammar.Incremental.implementation
;;

let lex_and_parse_interface path : SurfaceSyntax.interface =
  mkprefix path @ lex_and_parse path Grammar.Incremental.interface
;;


(* -------------------------------------------------------------------------- *)

(* Filename handling, as well as include directories handling. *)

let include_dirs: string list ref =
  ref []
;;

let print_include_dirs () =
  String.concat "\n  " !include_dirs
;;

let add_include_dir dir =
  include_dirs := dir :: !include_dirs
;;

let module_name_for_file_path (f: string): Module.name =
  let f = Filename.basename f in
  let f = chop_mz_or_mzi f in
  Module.register f
;;

let find_in_include_dirs (filename: string): string =
  let module M = struct exception Found of string end in
  try
    List.iter (fun dir ->
      let open Filename in
      let dir =
        if is_relative dir then
          current_dir_name ^ dir_sep ^ dir
        else
          dir
      in
      let path = concat dir filename in
      if Sys.file_exists path then
        raise (M.Found path)
    ) !include_dirs;
    Log.error "Unable to find a file named %s" filename
  with M.Found s ->
    s
;;

let js_special_mname = Module.register "::toplevel"

let find_and_lex_interface m =
  let find_and_lex_interface_raw (mname: Module.name): SurfaceSyntax.interface =
    let filename = Module.print mname ^ ".mzi" in
    lex_and_parse_interface (find_in_include_dirs filename)
  in

  let find_and_lex_interface_memoized : Module.name -> SurfaceSyntax.interface =
    Module.memoize find_and_lex_interface_raw
  in

  if Module.equal m js_special_mname then
    find_and_lex_interface_raw m
  else
    find_and_lex_interface_memoized m
;;

let find_and_lex_implementation m =
  let find_and_lex_implementation_raw (mname: Module.name): SurfaceSyntax.implementation =
    let filename = Module.print mname ^ ".mz" in
    lex_and_parse_implementation (find_in_include_dirs filename)
  in

  let find_and_lex_implementation_memoized : Module.name -> SurfaceSyntax.implementation =
    Module.memoize find_and_lex_implementation_raw
  in

  if Module.equal m js_special_mname then
    find_and_lex_implementation_raw m
  else
    find_and_lex_implementation_memoized m
;;


(* -------------------------------------------------------------------------- *)

(* Main routines. *)

(* Check a module against its interface. Not related to importing an interface
 * or anything. *)
let check_interface env signature =
  KindCheck.check_interface (TypeCore.kenv env) signature;
  Interfaces.check env signature
;;


let import_dependencies_in_scope env deps =
  List.fold_left (fun env mname ->
    let iface = find_and_lex_interface mname in
    Interfaces.import_interface env mname iface
  ) env deps
;;


(* This performs the bulk of the work. *)
let check_implementation
    (mname: Module.name)
    (program: SurfaceSyntax.implementation)
    (interface: SurfaceSyntax.interface option) =

  let open ExpressionsCore in

  (* Find all the dependencies... *)
  Log.debug ~level:2 "\n%s***%s Computing dependencies for %a"
    Bash.colors.Bash.yellow Bash.colors.Bash.default
    Module.p mname;
  let deps = Modules.all_dependencies mname (fun mname' ->
    if Module.equal mname mname' then
      program
    else
      find_and_lex_interface mname')
  in

  (* And import them all in scope. *)
  Log.debug ~level:2 "\n%s***%s Importing the dependencies of %a in scope"
    Bash.colors.Bash.yellow Bash.colors.Bash.default
    Module.p mname;
  let env = TypeCore.empty_env in
  let env = import_dependencies_in_scope env deps in
  let env = TypeCore.enter_module env mname in

  (* First pass of kind-checking; it checks for unbound variables and variables
   * with the wrong kind. Use [env.kenv] that contains all dependencies. *)
  KindCheck.check_implementation (TypeCore.kenv env) program;

  (* We need to translate the program down to the internal syntax. The freshly
   * returned kind environment allows us to understand what names are exported
   * by the module. We don't store it in [env] (our type environment),
   * otherwise, the module could refer to itself! *)
  let program = TransSurface.translate_implementation (TypeCore.kenv env) program in

  (* [type_check env unit] type-checks the compilation unit [unit] within the
     environment [env], which describes the previous compilation units. It
     returns an extended environment (the old and new bindings). This is a *type*
     environment (it describes the permissions at the end, for every variable
     in scope). *)
  let rec type_check env program =
    match program with
    | ValueDefinitions decls :: blocks ->
        Log.debug ~level:2 "\n%s***%s Processing declarations:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          Expressions.ExprPrinter.pdefinitions (env, decls);

        (* Perform the actual checking. The binders in the declaration group
         * will be opened in [blocks] as well. *)
        let env, blocks, exports = TypeChecker.check_declaration_group env decls blocks in

        (* Record the exports. The exports are *not* qualified. *)
        let env = Exports.bind_implementation_values env exports in

        (* Move on to the rest of the blocks. *)
        type_check env blocks

    | DataTypeGroup group :: blocks ->
        Log.debug ~level:2 "\n%s***%s Processing data type group:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          KindPrinter.pgroup (env, group);

        (* The binders in the data type group will be opened in the rest of the
         * blocks. Also performs the actual binding in the data type group, as
         * well as the variance and fact inference. *)
        let env, blocks, vars, dc_exports =
          Expressions.bind_data_type_group_in_toplevel_items env group blocks
        in

        (* This implementation now exports types and data constructors. *)
        let env = Exports.bind_implementation_types env group vars dc_exports in

        (* Move on to the rest of the blocks. *)
        type_check env blocks

    | _ :: _ ->
        Log.error "The parser should forbid this"

    | [] ->
        (* Print some extra debugging information. *)
        Log.debug ~level:2 "\n%s***%s Done type-checking:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          MzPprint.pdoc
          (KindPrinter.print_kinds_and_facts, env);

        env
  in

  (* Type-check the implementation. *)
  Log.debug ~level:2 "\n%s***%s Type-checking the implementation of %a, \
      environment so far:\n\n%a"
    Bash.colors.Bash.yellow Bash.colors.Bash.default
    Module.p mname
    Types.TypePrinter.penv env;
  let env = type_check env program in
  (* [env] is the state of the world at the end of this module. *)

  (* And type-check the implementation against its own signature, if any. *)
  Log.debug ~level:2 "\n%s***%s Matching %a against its signature"
    Bash.colors.Bash.yellow Bash.colors.Bash.default
    Module.p mname;

  match interface with
  | Some interface ->
      (* If the function types are not syntactically equal, the decision
       * procedure for comparing those two types introduces internal names
       * that end polluting the resulting environment! So we only use that
       * "polluted" environment to perform interface-checking, we don't
       * actually return it to the driver, say, for printing. *)
      check_interface env interface
  | None ->
      env

  (* We used to check that after type-checking the current module, no other
   * signature was altered. We used to be able to alter other signatures as
   * exclusive values used to be export-able. We now require all exports to be
   * duplicable (enforced in [check_interface]) so this check is no longer
   * necessary. *)
;;


let just_print_interface (mname: Module.name) =

  let env = TypeCore.empty_env in

  (* Find all the dependencies... *)
  let deps = Modules.all_dependencies mname find_and_lex_interface in
  (* Add our interface at the end. *)
  let deps = deps @ [mname] in

  (* And import them all in scope. *)
  let env = import_dependencies_in_scope env deps in

  env
;;



(* Plug everything together and process a given file. *)
let process file_path =
  if not (Sys.file_exists file_path) then
    Log.error "File %s does not exist" file_path;

  if Filename.check_suffix file_path ".mz" then
    let program = lex_and_parse_implementation file_path in
    let mname = module_name_for_file_path file_path in
    let iface =
      let iface_path = file_path ^ "i" in
      if Sys.file_exists iface_path then
        Some (lex_and_parse_interface iface_path)
      else
        None
    in
    let env = check_implementation mname program iface in
    if !Options.please_compile then
      Compile.implementation file_path program iface;
    env
  else if Filename.check_suffix file_path ".mzi" then
    let mname = module_name_for_file_path file_path in
    just_print_interface mname
  else
    Log.error "Unknown file extension"
;;

(* The [run] function serves as a wrapper that catches errors and prints them
 * properly (at the cost of losing a useful backtrace, though). *)
type run_options = {
  html_errors: bool;
  backtraces: bool;
}

let run { html_errors; backtraces } f =
  try
    f ()
  with
  | TypeErrors.TypeCheckerError e as the_exn ->
      if html_errors then begin
        TypeErrors.html_error e
      end else begin
        MzString.beprintf "%a\n" TypeErrors.print_error e;
      end;
      if backtraces then
        raise the_exn;
      exit 251
  | KindCheck.KindError e as the_exn ->
      MzString.beprintf "%a\n" e ();
      if backtraces then
        raise the_exn;
      exit 250
;;


(* A fancy version of [TypePrinter.penv]. It will *not* generate a valid .mzi
 * file, but it will give a somehow readable version of all the names that have
 * been defined in the environment as well as the type available for them. *)
let print_signature (buf: Buffer.t) (env: TypeCore.env): unit =
  let open TypeCore in
  let open Kind in
  let exports = KindCheck.get_exports (TypeCore.kenv env) in
  List.iter (fun (name, var) ->
    if get_kind env var = KValue then
      let perms = get_permissions env var in
      let perms =
        List.filter (function TyUnknown | TySingleton _ -> false | _ -> true) perms
      in
      List.iter (fun t ->
        let open MzPprint in
        (* First try to fold the type (e.g. turn "(=x, =y)" into "(int, int)"). *)
        let t = ResugarFold.fold_type env t in
        (* And then try to convert it to the surface syntax. *)
        let t = SurfaceSyntaxPrinter.print (Resugar.resugar env t) in
        (* Print it! *)
        pdoc buf ((fun () ->
          string "val" ^^ space ^^
          string (Variable.print name) ^^
          space ^^ at ^^ space ^^ (nest 2 t) ^^
          break 1
        ), ())
      ) perms
  ) exports
;;

(* -------------------------------------------------------------------------- *)

(* A driver for the interpreter. *)

let interpret (file_path : string) : unit =

  (* Check that this file exists and ends in [.mz]. *)

  if not (Sys.file_exists file_path) then
    Log.error "File %s does not exist" file_path;
  if not (Filename.check_suffix file_path ".mz") then
    Log.error "Unknown file extension";

  (* Determine the module name [m]. *)

  let m = module_name_for_file_path file_path in

  (* Find the modules that [m] depends upon. *)

  (* There is a fine var here. We are interested in the dependencies
     of an [.mz] file on another [.mz] file, because a module cannot be
     evaluated unless the modules that it refers to have been evaluated
     as well. This is in contrast with the type-checker and compiler,
     which look for dependencies of an [.mz] file on an [.mzi] file;
     we have separate type-checking and compilation. *)

  let ms : Module.name list =
    Modules.all_dependencies m find_and_lex_implementation in
  (* TEMPORARY detect cyclic dependencies *)

  (* Evaluate each of these modules in turn. *)

  let env : Interpreter.env =
    List.fold_left (fun env m ->

      (* We assume that each module consists of an interface file
        and an implementation file. The interface file serves a
         role as a filter (not all definitions are exported), so
         it cannot be disregarded. *)
      Interpreter.eval_unit
        env
        m
        (find_and_lex_interface m)
        (find_and_lex_implementation m)

    ) Interpreter.empty ms
  in

  (* Evaluate [m] itself. Here, we do not care whether there is
     or isn't an [.mzi] file. We evaluate the implementation, and
     we are done. *)

  Interpreter.eval_lone_implementation
    env
    (find_and_lex_implementation m)
