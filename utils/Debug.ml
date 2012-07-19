open Types
open TypePrinter
open Bash

let enabled = ref "";;
let enable_trace v = enabled := v;;

module Graph = struct

  let id_of_point env point: int =
    let p = PersistentUnionFind.repr point env.state in
    Obj.magic p
  ;;

  let draw_point buf env point permissions =
    let id = id_of_point env point in
    let names = Hml_List.map_some
      (function User v -> Some (Variable.print v) | Auto _ -> None)
      (get_names env point)
    in
    let names = String.concat " = " names in

    (* Get a meaningful type. *)
    let t =
      try List.find (function TySingleton (TyPoint _) -> false | _ -> true) permissions
      with _ -> TyUnknown
    in

    let gen env name t =
      let p' =
        match t with
        | TySingleton (TyPoint p') -> p'
        | _ -> Log.error "Need [unfold]"
      in
      let block = Printf.sprintf "<%s>%s" name name in
      let edge = (name, id_of_point env p') in
      block, edge
    in

    (* Get the various blocks and edges that we should draw. *)
    let line, edges =
      match t with
      | TyConcreteUnfolded (datacon, fields) ->
          let blocks, edges = List.split (List.map (fun f ->
            let name, t =
              match f with
              | FieldValue (name, t) ->
                  Field.print name, t
              | _ ->
                  Log.error "Need [collect]"
            in
            gen env name t
          ) fields) in
          let blocks =
            if List.length blocks > 0 then
              "|" ^ String.concat "|" blocks
            else
              ""
          in
          Datacon.print datacon ^ blocks, edges

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
          let s = Hml_String.bsprintf "%a" ptype (env, t) in
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
    let env = TypeOps.mark_reachable env (TyPoint root) in
    fold_terms env (fun () point _head { permissions; _ } ->
      if is_marked env point then
        draw_point buf env point permissions
    ) ();
    write_outro buf;
  ;;

  let write_graph buf env =
    write_intro buf;
    fold_terms env (fun () point _head { permissions; _ } ->
      draw_point buf env point permissions
    ) ();
    write_outro buf;
  ;;

  let graph env =
    let ic, oc = Unix.open_process "dot -Tx11" in
    Hml_String.bfprintf oc "%a" write_graph env;
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
    fold_terms env (fun json point { names; locations; kind; _ } { permissions; _ } ->
      let open TypePrinter in
      let names = `List (List.map (function
        | User v -> `List [`String "user"; `String (Variable.print v)]
        | Auto v -> `List [`String "auto"; `String (Variable.print v)]
      ) names) in
      let locations = `List (List.map json_of_loc locations) in
      let kind = `String (Hml_String.bsprintf "%a" pdoc (print_kind, kind)) in
      let permissions = `List (List.map (fun perm ->
        `String (Hml_String.bsprintf "%a" ptype (env, perm))
      ) permissions) in
      (string_of_int (Graph.id_of_point env point), `Assoc [
        ("names", names);
        ("locations", locations);
        ("kind", kind);
        ("permissions", permissions);
      ]) :: json
    ) []
  ;;

  let render_svg env =
    (* Create the SVG. *)
    let ic, oc = Unix.open_process "dot -Tsvg" in
    Hml_String.bfprintf oc "%a" Graph.write_graph env;
    close_out oc;
    let svg = Utils.read ic in
    close_in ic;
    svg
  ;;

  let render_base env extra =
    (* Create the syntax-highlighted HTML. *)
    let f = (fst env.location).Lexing.pos_fname in
    let syntax = pygmentize f in

    (* Create the JSON data. *)
    let json = `Assoc ([
      ("syntax", `String syntax);
      ("current_location", json_of_loc env.location);
      ("file_name", `String f);
    ] @ extra) in

    (* Output it to a file. *)
    let json_file =
      let f = Hml_String.replace "/" "_" f in
      Printf.sprintf "viewer/data/%s.json" f
    in
    let oc = open_out json_file in
    Yojson.Safe.to_channel oc json;
    close_out oc;
  ;;

  let render env =
    Hml_Pprint.disable_colors ();

    let extra = [
      ("type", `String "single");
      ("svg", `String (render_svg env));
      ("points", `Assoc (json_of_points env));
    ] in

    render_base env extra;

    Hml_Pprint.enable_colors ();
  ;;

  let render_merge env sub_envs =
    Hml_Pprint.disable_colors ();

    let render_env_point (env, point) =
      `Assoc [
        ("svg", `String (render_svg env));
        ("root", `Int (Graph.id_of_point env point));
        ("points", `Assoc (json_of_points env));
        ("dot", `String (Hml_String.bsprintf "%a" Graph.write_graph env));
      ]
    in

    (* Create the JSON data. *)
    let extra = [
      ("type", `String "merge");
      ("merged_env", render_env_point env);
      ("sub_envs", `List (List.map render_env_point sub_envs));
    ] in

    render_base (fst env) extra;

    Hml_Pprint.enable_colors ();
  ;;

end


let explain env x =
  if !enabled = "html" then
    Html.render env;
  if !enabled = "x11" then begin
    (* Reset the screen. *)
    flush stdout; flush stderr;
    reset ();

    (* Print the current position. *)
    Hml_String.bprintf "Last checked expression: %a at %a\n"
      pnames (get_names env x)
      Lexer.p env.location;

    (* Print MOAR. *)
    Hml_String.bprintf "\n";
    Hml_String.bprintf "%a\n\n" ppermissions env;
    Hml_String.bprintf "%s\n\n" (String.make twidth '-');
    flush stdout; flush stderr;
    Graph.graph env
  end
;;


let explain_merge env sub_envs =
  if !enabled = "html" then
    Html.render_merge env sub_envs;
;;
