open Types
open TypePrinter
open Bash

let enabled = ref false;;
let enable_trace v = enabled := v;;

module Graph = struct

  let id_of_point env point: int =
    let p = PersistentUnionFind.repr point env.state in
    Obj.magic p
  ;;

  let draw_point oc env point permissions =
    let id = id_of_point env point in
    let names = List.map (Variable.print) (get_names env point) in
    let names = List.filter (fun x -> x.[0] != '/') names in
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
          Datacon.print datacon ^ "|" ^ String.concat "|" blocks, edges

      | TyTuple ts ->
          let blocks, edges = List.split (List.mapi (fun i t ->
            let name = Printf.sprintf "_%d" i in
            gen env name t
          ) ts) in
          String.concat "|" blocks, edges

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
            if String.length s > 50 then
              String.sub s 0 50 ^ "…"
            else
              s
          in
          (* Done. *)
          s, []
    in

    (* Print the edges *)
    List.iter (fun (field, dest) ->
      Printf.fprintf oc "\"node%d\":%s -> \"node%d\" [\n" id field dest;
      (* Printf.fprintf oc "id = 6\n"; *)
      Printf.fprintf oc "];\n";
    ) edges;

    (* Print the node. *)
    Printf.fprintf oc "\"node%d\" [\n" id;
    if String.length names > 0 then
      Printf.fprintf oc "  label = \"{{%s}|%s}\"\n" line names
    else
      Printf.fprintf oc "  label = \"%s\"\n" line;
    Printf.fprintf oc "  shape = \"record\"\n";
    Printf.fprintf oc "];\n";
  ;;

  let write_intro oc =
    Printf.fprintf oc "digraph g {\n";
    Printf.fprintf oc "graph [\n";
    Printf.fprintf oc "  rankdir = \"BT\"\n";
    Printf.fprintf oc "];\n";
  ;;

  let write_outro oc =
    Printf.fprintf oc "}";
  ;;

  let graph env =
    let filename = Filename.temp_file "hamlet" ".dot" in
    let oc = open_out filename in
    write_intro oc;
    fold_terms env (fun () point _head { permissions; _ } ->
      draw_point oc env point permissions
    ) ();
    write_outro oc;
    close_out oc;
    let err = Sys.command (Printf.sprintf "dot -Tx11 %s" (Filename.quote filename)) in
    if err = 0 then
      Unix.unlink filename;
  ;;

end

let explain env x =
  if !enabled then begin
    (* Reset the screen. *)
    flush stdout; flush stderr;
    reset ();

    (* Print the current position. *)
    Hml_String.bprintf "Last checked expression: %a at %a\n"
      pnames (get_names env x)
      Lexer.p env.position;

    (* Print MOAR. *)
    Hml_String.bprintf "\n";
    Hml_String.bprintf "%a\n\n" ppermissions env;
    Hml_String.bprintf "%s\n\n" (String.make twidth '-');
    flush stdout; flush stderr;
    Graph.graph env
  end
;;
