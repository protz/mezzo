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

(* -------------------------------------------------------------------------- *)

(* Lexing and parsing, built on top of [grammar]. *)

let lex_and_parse file_path entry_var =
  Utils.with_open_in file_path (fun file_desc ->
  let lexbuf = Ulexing.from_utf8_channel file_desc in
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised entry_var in
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
    | Grammar.Error ->
        MzString.beprintf "%a\nError: Syntax error\n"
          print_position lexbuf;
        exit 253
    | Lexer.LexingError e ->
        MzString.beprintf "%a\n"
          Lexer.print_error (lexbuf, e);
        exit 252
  )
;;

let mkprefix path =
  if !Options.no_auto_include && path = !Options.filename then
    []
  else
    let corelib_dir =
      Filename.concat Configure.root_dir "corelib"
    in
    let autoload_path = Filename.concat corelib_dir "autoload" in
    let autoload_modules = MzString.split (Utils.file_get_contents autoload_path) '\n' in
    let autoload_modules = List.filter (fun s -> String.length s > 0 && s.[0] <> '#') autoload_modules in
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
    let me_in_core_directory =
         Utils.same_absolute_path  corelib_dir              my_dir
      || Utils.same_absolute_path (corelib_dir ^ "/_build") my_dir
    in
    Log.debug "In core directory? %b" me_in_core_directory;
    let modules =
      if me_in_core_directory then
        chop autoload_modules
      else
        autoload_modules
    in
    List.map (fun x ->
      SurfaceSyntax.OpenDirective (Module.register x)
    ) modules 
;;

let lex_and_parse_implementation path : SurfaceSyntax.implementation =
  mkprefix path @ lex_and_parse path Grammar.implementation
;;

let lex_and_parse_interface path : SurfaceSyntax.interface =
  mkprefix path @ lex_and_parse path Grammar.interface
;;


(* -------------------------------------------------------------------------- *)

(* Filename handling, as well as include directories handling. *)

let include_dirs: string list ref =
  ref []
;;

let add_include_dir dir =
  include_dirs := dir :: !include_dirs
;;

let module_name_for_file_path (f: string): Module.name =
  let f = Filename.basename f in
  let f =
    if Filename.check_suffix f ".mz" then
      Filename.chop_suffix f ".mz"
    else if Filename.check_suffix f ".mzi" then
      Filename.chop_suffix f ".mzi"
    else
      Log.error "This is unexpected"
  in
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

let find_and_lex_interface : Module.name -> SurfaceSyntax.interface =
  Module.memoize (fun mname ->
    let filename = Module.print mname ^ ".mzi" in
    lex_and_parse_interface (find_in_include_dirs filename)
  )
;;

let find_and_lex_implementation : Module.name -> SurfaceSyntax.implementation =
  Module.memoize (fun mname ->
    let filename = Module.print mname ^ ".mz" in
    lex_and_parse_implementation (find_in_include_dirs filename)
  )
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
    | DataTypeGroup group :: blocks ->
        Log.debug ~level:2 "\n%s***%s Processing data type group:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          KindPrinter.pgroup (env, group);

        (* The binders in the data type group will be opened in the rest of the
         * blocks. Also performs the actual binding in the data type group, as
         * well as the variance and fact inference. *)
        let env, blocks, _ =
          Expressions.bind_data_type_group_in_toplevel_items env group blocks
        in
        (* Move on to the rest of the blocks. *)
        type_check env blocks
    | ValueDefinitions decls :: blocks ->
        Log.debug ~level:2 "\n%s***%s Processing declarations:\n%a"
          Bash.colors.Bash.yellow Bash.colors.Bash.default
          Expressions.ExprPrinter.pdefinitions (env, decls);

        (* Perform the actual checking. The binders in the declaration group
         * will be opened in [blocks] as well. *)
        let env, blocks, exports = TypeChecker.check_declaration_group env decls blocks in

        (* Record the exports. The exports are *not* qualified. *)
        let env = TypeCore.modify_kenv env (fun kenv k ->
          let kenv = List.fold_left (fun kenv (name, var) ->
            KindCheck.bind_nonlocal kenv (name, Kind.KTerm, var)
          ) kenv exports in
          k kenv (fun env -> env)
        ) in

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
  flush stdout;
  flush stderr;
  let open TypeCore in
  let compare_locs loc1 loc2 =
    Lexing.(compare loc1.pos_cnum loc2.pos_cnum)
  in
  let perms = fold_terms env (fun acc var permissions ->
    let locations = get_locations env var in
    let locations = List.sort (fun (loc1, _) (loc2, _) -> compare_locs loc1 loc2) locations in
    let location = fst (List.hd locations) in
    List.map (fun x -> var, location, x) permissions :: acc
  ) [] in
  let perms = List.flatten perms in
  let perms = List.filter (fun (var, _, perm) ->
    match perm with
    | TyUnknown ->
        false
    | TySingleton (TyOpen var') when same env var var' ->
        false
    | _ ->
        true
  ) perms in
  let perms = List.sort (fun (_, loc1, _) (_, loc2, _) -> compare_locs loc1 loc2) perms in
  List.iter (fun (var, _, t) ->
    let open Types.TypePrinter in
    let open MzPprint in
    try
      let name = List.find (function
        | User (m, x) ->
            Module.equal m (module_name env) &&
            (Variable.print x).[0] <> '/'
        | Auto _ ->
            false
      ) (get_names env var) in
      let t =
        match TypeErrors.fold_type env t with
        | Some t ->
            t
        | None ->
            Log.warn "Badly printed type, sorry about that!";
            t
      in
      pdoc buf ((fun () ->
        let t =
          if true (* TEMPORARY *) then 
            print_type env t
          else
            SurfaceSyntaxPrinter.print (Resugar.resugar env t)
        in
        string "val" ^^ space ^^
        print_var env name ^^ space ^^ at ^^ space ^^ (nest 2 t) ^^
        break 1
      ), ())

    with Not_found ->
      ()
  ) perms
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

