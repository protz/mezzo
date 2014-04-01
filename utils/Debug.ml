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

open Kind
open TypeCore
open Types
open TypePrinter
open Bash

(* An environment annotated with a list of conflicting variables. *)
type cenv = (env * var) * var list

let enabled = ref "";;
let enable_trace v = enabled := v;;
let is_osx =
  lazy begin
    Sys.os_type = "Unix" &&
    String.sub (Ocamlbuild_plugin.run_and_read "uname") 0 6 = "Darwin"
  end
;;

let unique xs =
  let xs = List.sort compare xs in
  let rec loop xs x1 = function
    | [] ->
        List.rev (x1 :: xs)
    | x2 :: rest ->
        if x1 = x2 then
          loop xs x1 rest
        else
          loop (x1 :: xs) x2 rest
  in
  match xs with
  | [] ->
      []
  | x1 :: rest ->
      loop [] x1 rest
;;

module Graph = struct

  let id_of_point env var: int =
    internal_uniqvarid env var
  ;;

  let draw_point buf env point is_conflict permissions =
    let id = id_of_point env point in

    let names = MzList.map_some
      (function
        | User (m, v) ->
            if Module.equal m (module_name env) then
              Some (Variable.print v)
            else
              Some (Module.print m ^ "::" ^ Variable.print v)
        | Auto _ -> None)
      (get_names env point)
    in
    let names = unique names in
    let names = String.concat " = " names in

    (* Get a meaningful type. *)
    let permissions = 
      let sort = function
        | TyDynamic -> 2
        | TyUnknown -> 3
        | TySingleton _ -> 4
        | _ -> 1
      in
      let sort x y = sort x - sort y in
      List.sort sort permissions
    in
    let t = List.hd permissions in

    (* When generating a block (tuple, record), this function, for each =x
     * found inside the tuple or record, will generate the corresponding dot
     * sub-string that stands for the field, as well as a pair of the field name
     * and the dot node id that it should point to. *)
    let gen env name t =
      let p' =
        (* The call to modulo_flex is required so that we get the "actual" id,
         * not the one of an instantiated flexible variable. *)
        match t with
        | TySingleton t -> !!(modulo_flex env t)
        | _ -> Log.error "Need [unfold]"
      in
      let block = Printf.sprintf "<%s>%s" name name in
      let edge = (name, id_of_point env p') in
      block, edge
    in

    (* Get the various blocks and edges that we should draw. *)
    let line, edges =
      match t with
      | TyConcrete { branch_datacon; branch_fields; _ } ->
          let blocks, edges = MzList.split_map (fun (name, t) ->
            let name = Field.print name in
            gen env name t
          ) branch_fields in
          let blocks =
            if List.length blocks > 0 then
              "|" ^ String.concat "|" blocks
            else
              ""
          in
          Datacon.print (snd branch_datacon) ^ blocks, edges

      | TyTuple ts ->
          let blocks, edges = List.split (List.mapi (fun i t ->
            let name = Printf.sprintf "_%d" i in
            gen env name t
          ) ts) in
          let line =
            if List.length blocks > 0 then
              String.concat "|" blocks
            else
              "()"
          in
          line, edges

      | _ ->
          (* Dump the type as a string. *)
          let s = MzString.bsprintf "%a" ptype (env, t) in
          (* Collapse whitespace. *)
          let regexp = Str.regexp " +" in
          let s = Str.global_replace regexp " " s in
          (* Remove newlines. *)
          let regexp = Str.regexp "\n" in
          let s = Str.global_replace regexp "" s in
          (* Quote special characters. *)
          let regexp = Str.regexp "[<>| {}]" in
          let s = Str.global_replace regexp "\\\\\\0" s in
          (* Trim the string to a reasonable length. *)
          let s =
            if String.length s > 30 then
              String.sub s 0 30 ^ "…"
            else
              s
          in
          (* Done. *)
          s, []
    in

    (* Print the edges *)
    List.iter (fun (field, dest) ->
      Printf.bprintf buf "\"node%d\":%s -> \"node%d\" [\n" id field dest;
      (* Printf.fprintf oc "id = 6\n"; *)
      Printf.bprintf buf "];\n";
    ) edges;

    (* Print the node. *)
    Printf.bprintf buf "\"node%d\" [\n" id;
    Printf.bprintf buf "  id = \"node%d\"\n" id;
    if is_conflict then
      Printf.bprintf buf "  color = \"#B00040\"\n";
    if String.length names > 0 then
      Printf.bprintf buf "  label = \"{{%s}|%s}\"\n" line names
    else
      Printf.bprintf buf "  label = \"%s\"\n" line;
    Printf.bprintf buf "  shape = \"record\"\n";
    Printf.bprintf buf "];\n";
  ;;

  let write_intro buf =
    Printf.bprintf buf "digraph g {\n";
    Printf.bprintf buf "graph [\n";
    Printf.bprintf buf "  rankdir = \"BT\"\n";
    Printf.bprintf buf "];\n";
  ;;

  let write_outro buf =
    Printf.bprintf buf "}";
  ;;

  let write_simple_graph buf (env, root) =
    write_intro buf;
    let env = refresh_mark env in
    let env = mark_reachable env (TyOpen root) in
    fold_terms env (fun () var permissions ->
      if is_marked env var then
        draw_point buf env var false permissions
    ) ();
    write_outro buf;
  ;;

  (* Our criterion for marking "interesting" things is: everything that's a
   * structural permission + things that are pointed to by structural
   * permissions. This yields some "interesting" graphs. For some definition of
   * "interesting". *)
  let mark_interesting env conflicts =
    let env = refresh_mark env in
    let env = List.fold_left mark env conflicts in
    fold_terms env (fun env var permissions ->
      List.fold_left (fun env perm ->
        match perm with
        | TyConcrete { branch_fields; _ } ->
            if List.length branch_fields > 0 then
              let env = mark env var in
              List.fold_left (fun env (_, t) ->
                mark env !!=t
              ) env branch_fields
            else
              env
        | TyTuple ts ->
            if List.length ts > 0 then
              let env = mark env var in
              List.fold_left (fun env t -> mark env !!=t) env ts
            else
              env
        | _ ->
            env
      ) env permissions
    ) env
  ;;

  let write_graph buf (env, conflicts) =
    write_intro buf;
    let env = mark_interesting env conflicts in
    fold_terms env (fun () var permissions ->
      let is_conflict = List.exists (same env var) conflicts in
      let names = get_names env var in
      let in_current_module = function
        | Auto _ ->
            true
        | User (m, _) when Module.equal m (module_name env) ->
            true
        | _ ->
            false
      in
      if List.exists in_current_module names && is_marked env var then
        draw_point buf env var is_conflict permissions
    ) ();
    write_outro buf;
  ;;

  let graph env interesting =
    let ic, oc = Unix.open_process "dot -Tx11" in
    MzString.bfprintf oc "%a" write_graph (env, interesting);
    close_out oc;
    close_in ic;
  ;;

end


module Html = struct

  let pygmentize f =
    let cmd = Printf.sprintf "pygmentize -l ocaml -f html -O encoding=utf-8 %s" (Filename.quote f) in
    Ocamlbuild_plugin.run_and_read cmd
  ;;

  let json_of_loc loc =
    let open Lexing in
    let f pos =
      let line = pos.pos_lnum in
      let col = pos.pos_cnum - pos.pos_bol in
      `Assoc [("line", `Int line); ("col", `Int col)]
    in
    `Assoc [("start", f (fst loc)); ("end", f (snd loc))]
  ;;

  let json_of_points env =
    fold_terms env (fun json var permissions ->
      let names = get_names env var in
      let locations = get_locations env var in
      let kind = get_kind env var in
      let names = `List (List.map (function
        | User (_, v) -> `List [`String "user"; `String (Variable.print v)]
        | Auto v -> `List [`String "auto"; `String (Variable.print v)]
      ) names) in
      let locations = `List (List.map json_of_loc locations) in
      let kind = `String (MzString.bsprintf "%a" MzPprint.pdoc (print_kind, kind)) in
      let permissions = `List (List.map (fun perm ->
        `String (MzString.bsprintf "%a" ptype (env, perm))
      ) permissions) in
      (string_of_int (Graph.id_of_point env var), `Assoc [
        ("names", names);
        ("locations", locations);
        ("kind", kind);
        ("permissions", permissions);
      ]) :: json
    ) []
  ;;

  let render_svg env conflicts =
    (* Create the SVG. *)
    let ic, oc = Unix.open_process "dot -Tsvg" in
    MzString.bfprintf oc "%a" Graph.write_graph (env, conflicts);
    close_out oc;
    let svg = Utils.read ic in
    close_in ic;
    (* MzString.bprintf "%a" Graph.write_graph (env, conflicts); *)
    svg
  ;;

  let get_json_filename env =
    let f = (fst (location env)).Lexing.pos_fname in
    let f = MzString.replace "/" "_" f in
    (* FIXME use Filename + temp_dir + properly package the viewer *)
    Printf.sprintf "%s/viewer/data/%s.json" Configure.lib_dir f
  ;;

  let render_base env extra =
    (* Create the syntax-highlighted HTML. *)
    let f = (fst (location env)).Lexing.pos_fname in
    let syntax = pygmentize f in

    (* Create the JSON data. *)
    let json = `Assoc ([
      ("syntax", `String syntax);
      ("current_location", json_of_loc (location env));
      ("file_name", `String f);
    ] @ extra) in

    (* Output it to a file. *)
    let json_file = get_json_filename env in
    let oc = open_out json_file in
    Yojson.Safe.to_channel oc json;
    close_out oc;
  ;;

  let render env text interesting =
    MzPprint.disable_colors ();

    let extra = [
      ("type", `String "single");
      ("svg", `String (render_svg env interesting));
      ("points", `Assoc (json_of_points env));
      ("error_message", `String text);
    ] in

    render_base env extra;

    MzPprint.enable_colors ();
  ;;

  let render_merge (env: cenv) (sub_envs: cenv list) =
    MzPprint.disable_colors ();

    let render_env_point ((env, point), conflicts) =
      `Assoc [
        ("svg", `String (render_svg env conflicts));
        ("root", `Int (Graph.id_of_point env point));
        ("points", `Assoc (json_of_points env));
        ("dot", `String (MzString.bsprintf "%a" Graph.write_graph (env, conflicts)));
      ]
    in

    (* Create the JSON data. *)
    let extra = [
      ("type", `String "merge");
      ("merged_env", render_env_point env);
      ("sub_envs", `List (List.map render_env_point sub_envs));
    ] in

    render_base (fst (fst env)) extra;

    MzPprint.enable_colors ();
  ;;

  let launch env =
    if not Configure.has_firefox then
      Log.error "Firefox was not detected for the -explain html feature.";
    if Unix.fork () = 0 then begin
      (* This now is an absolute path *)
      let filename = get_json_filename env in
      let page = 
        Printf.sprintf "file://%s/viewer/viewer.html?json_file=%s"
          Configure.lib_dir filename;
      in
      if !*is_osx then
        Unix.execvp "open" [| "open"; "-a"; Configure.firefox; "--args"; page |]
      else
        Unix.execvp Configure.firefox [| Configure.firefox; "-new-window"; page |]
    end;
  ;;

end


let explain ?(text="") ?x env =
  (* By default, explanations print verbose information if debug is enabled, and
   * a short summary (always). *)
  Option.iter (fun x ->
    Log.debug ~level:1 "Debug is enabled, here's some verbose information.";
    Log.debug ~level:1 "Last checked expression: %a at %a\n"
      pnames (env, get_names env x)
      Lexer.p (location env);

    Log.debug ~level:1 "\n";
    Log.debug ~level:1 "%a\n\n" ppermissions env;
    Log.debug ~level:1 "%s\n\n%!" (String.make twidth '-');

    MzString.bprintf "%a\n%!" DerivationPrinter.psummary (env, x);
  ) x;

  (* If we're given a specific variable, then it's an interesting one, and it
   * should be highlighted in whatever format we want. *)
  let interesting = Option.to_list x in
  if !enabled = "html" then begin
    Html.render env text interesting;
    Html.launch env;
  end else if !enabled = "x11" then begin
    Graph.graph env interesting
  end
;;

let explain_merge (env: cenv) (sub_envs: cenv list) =
  if !enabled = "html" then begin
    Html.render_merge env sub_envs;
    Html.launch (fst (fst env));
  end
;;
