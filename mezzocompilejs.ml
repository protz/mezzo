#use "mezzofiles.ml"
let all = List.flatten (List.map (fun (dir,files) ->
    List.map (fun file ->
        dir ^ "/" ^ file ^ ":/") files
  ) all)

let args = List.map (fun s -> "-file "^s) all
let s = String.concat " " args
let _ = print_string s
let _ = flush_all ()
