type kind =
  | KTerm
  | KType
  | KPerm
  | KArrow of kind * kind

let as_arrow k =
  let rec as_arrow accu = function
    | KArrow (k1, k2) ->
        as_arrow (k1 :: accu) k2
    | k ->
        List.rev accu, k
  in
  as_arrow [] k

let arity k =
  let rec arity accu = function
    | KArrow (_, k2) ->
        arity (1 + accu) k2
    | _ ->
        accu
  in
  arity 0 k

let rec print =
  function
  | KTerm ->
      "term"
  | KPerm ->
      "perm"
  | KType ->
      "type"
  | KArrow (k1, k2) ->
      (* No parentheses required; first-order kinds only. *)
      print k1 ^ " -> " ^ print k2

let print_kind k =
  PPrint.string (print k)

