#use "mezzofiles.ml"
(* TEMPORARY this file will go away as soon as we switch
   to the next version of js_of_ocaml *)
let all = List.flatten (List.map (fun (dir,files) ->
    List.map (fun file ->
        dir ^ "/" ^ file ^ ":/") files
  ) all)

let args = List.map (fun s -> "-file "^s) all
let s = String.concat " " args
let _ = print_string s
let _ = flush_all ()
