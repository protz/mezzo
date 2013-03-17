(* Kinds. *)

(* Arrow kinds are not accessible to the user. They are used internally:
   a user-defined algebraic data type constructor receives an arrow kind.
   Thus, even internally, we only use first-order kinds (that is, the
   left-hand argument of an arrow kind is never itself an arrow kind). *)

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
