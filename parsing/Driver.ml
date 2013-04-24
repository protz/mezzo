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
let check_interface env signature exports =
  KindCheck.check_interface (KindCheckGlue.initial env) signature;
  (* It may very well be that [Interfaces.check] subsumes what
   * [KindCheck.check_interface] does. *)
  Interfaces.check env signature exports
;;


let import_dependencies_in_scope env deps =
  List.fold_left (fun env mname ->
    let iface = find_and_lex_interface mname in
    let env = Interfaces.import_interface env mname iface in
    Log.debug "Imported %a, got names %a"
      Module.p mname
      Types.TypePrinter.pexports (env, mname);
    env
  ) env deps
;;


(* This performs the bulk of the work. *)
let check_implementation
    (mname: Module.name)
    (program: SurfaceSyntax.implementation)
    (interface: SurfaceSyntax.interface option) =

  let open Expressions in

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
  let env = TypeCore.set_module_name env mname in

  (* Build a kind-checking environment out of this type environment. We could
     bypass this if we had a version of [import_dependencies_in_scope] that
     constructed a kind-checking environment... TEMPORARY *)
  let kenv = KindCheckGlue.initial env in

  (* First pass of kind-checking; it checks for unbound variables and variables
   * with the wrong kind. *)
  KindCheck.check_implementation kenv program;

  (* We need to translate the program down to the internal syntax. *)
  let program = TransSurface.translate_implementation kenv program in

  (* [type_check] also returns a list of vars, with the property that if x
   * comes later than y in the file, then the var associated to x will come
   * before that of y in the list of vars. *)
  let type_check env program =
    let rec type_check env program varss =
      match program with
      | DataTypeGroup group :: blocks ->
          Log.debug ~level:2 "\n%s***%s Processing data type group:\n%a"
            Bash.colors.Bash.yellow Bash.colors.Bash.default
            KindPrinter.pgroup (env, group);

          (* The binders in the data type group will be opened in the rest of the
           * blocks. Also performs the actual binding in the data type group, as
           * well as the variance and fact inference. *)
          let env, blocks, vars = DataTypeGroup.bind_data_type_group env group blocks in
          (* Move on to the rest of the blocks. *)
          type_check env blocks (vars :: varss)
      | ValueDefinitions decls :: blocks ->
          Log.debug ~level:2 "\n%s***%s Processing declarations:\n%a"
            Bash.colors.Bash.yellow Bash.colors.Bash.default
            Expressions.ExprPrinter.pdefinitions (env, decls);

          (* Perform the actual checking. The binders in the declaration group
           * will be opened in [blocks] as well. *)
          let env, blocks, vars = TypeChecker.check_declaration_group env decls blocks in
          (* Move on to the rest of the blocks. *)
          type_check env blocks (vars :: varss)
      | _ :: _ ->
          Log.error "The parser should forbid this"
      | [] ->
          (* Print some extra debugging information. *)
          Log.debug ~level:2 "\n%s***%s Done type-checking:\n%a"
            Bash.colors.Bash.yellow Bash.colors.Bash.default
            MzPprint.pdoc
            (KindPrinter.print_kinds_and_facts, env);

          env, List.flatten varss
    in
    type_check env program []
  in

  (* Type-check the implementation. *)
  Log.debug ~level:2 "\n%s***%s Type-checking the implementation of %a, \
      environment so far:\n\n%a"
    Bash.colors.Bash.yellow Bash.colors.Bash.default
    Module.p mname
    Types.TypePrinter.penv env;
  let env, vars = type_check env program in

  (* And type-check the implementation against its own signature, if any. *)
  Log.debug ~level:2 "\n%s***%s Matching %a against its signature"
    Bash.colors.Bash.yellow Bash.colors.Bash.default
    Module.p mname;
  let output_env =
    match interface with
    | Some interface ->
        (* We cannot use [Types.get_exports] here because we may have the same
         * name at top-level twice, and [Types.get_exports] doesn't know which
         * one ends up being exported. Instead, we can rely on [type_check] to
         * returns for us the list of names along with the corresponding vars
         * that are exported. *)
        let exports = MzList.map_flatten (fun p ->
          let k = TypeCore.get_kind env p in
          MzList.map_some (function
            | TypeCore.User (mname, x) when Module.equal mname (TypeCore.module_name env) ->
               Some (x, k, p)
            | _ ->
               (* Either an auto-generated name, or a name coming from another
                * module. Think about a top-level definition such as:
                *   let x = m::y
                * we just drop the name "y" here. *)
               None
          ) (TypeCore.get_names env p)
        ) vars in
        (* If the function types are not syntactically equal, the decision
         * procedure for comparing those two types introduces internal names
         * that end polluting the resulting environment! So we only use that
         * "polluted" environment to perform interface-checking, we don't
         * actually return it to the driver, say, for printing. *)
        check_interface env interface exports
    | None ->
        env
  in

  (* Check that the implementation leaves all other modules intact (matching
   * against the signature right above may have consumed permissions from other
   * modules!) *)
  if not !Options.no_sig_check then begin
    Log.debug ~level:2 "\n%s***%s Checking %a does not alter other interfaces"
      Bash.colors.Bash.yellow Bash.colors.Bash.default
      Module.p mname;
    List.iter (fun mname ->
      Log.debug ~level:2 "\n%s***%s Checking against %a"
        Bash.colors.Bash.yellow Bash.colors.Bash.default
        Module.p mname;
      let iface = find_and_lex_interface mname in
      (* Ignore the interface, since there's no risk of an interface consuming
       * another interface's contents! Moreover, this can be a risk: since
       * [check_interface] has the nasty consequence that the [env] it returns is
       * polluted with internal names (the result of performing calls to
       * [Permissions.sub]), opening the same module twice may cause conflicts... *)
      (* TEMPORARY this also creates problems when passing the polluted environment
        to [KindCheck.initial]. I suggest it would be simpler to just require that
        everything published in an interface be duplicable. *)
      let exports = TypeCore.get_exports env mname in
      ignore (check_interface output_env iface exports)
    ) deps;

    env
  end else begin
    env
  end
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

