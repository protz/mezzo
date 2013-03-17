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

(* A small helper function that transforms
 * [κ₁ → ... → κₙ → κ₀] into [κ₀, [κ₁; ...; κₙ]] *)
let flatten_kind kind =
  let rec flatten_kind acc = function
    | KArrow (k1, k2) ->
        flatten_kind (k1 :: acc) k2
    | _ as k ->
        acc, k
  in
  let acc, k = flatten_kind [] kind in
  k, List.rev acc
;;

let get_arity_for_kind kind =
  let _, tl = flatten_kind kind in
  List.length tl
;;

