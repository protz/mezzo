open Types

let print_env (env: env) =
  let open TypePrinter in
  Log.debug ~level:1 "%a\n" pdoc (print_permissions, env);
;;

(* Some OCaml functions that create HaMLeT types. *)

let cons (head, tail) =
  TyConcreteUnfolded (Datacon.register "Cons",
    [FieldValue (Field.register "head", head);
     FieldValue (Field.register "tail", tail)])
;;

let nil =
  TyConcreteUnfolded (Datacon.register "Nil", [])
;;

let tuple l =
  TyTuple l
;;

let point x =
  TyPoint x
;;

let points_to x =
  TySingleton (point x)
;;

let permission (p, x) =
  TyAnchoredPermission (p, x)
;;

let forall (x, k) t =
  TyForall (((User (Variable.register x), k, (Lexing.dummy_pos, Lexing.dummy_pos)), CanInstantiate), t)
;;

let var x =
  TyVar x
;;

(* This is right-associative, so you can write [list int @-> int @-> tuple []] *)
let (@->) x y =
  TyArrow (x, y)
;;

let ktype =
  SurfaceSyntax.KType
;;

let unit =
  tuple []
;;

let datacon d f =
  TyConcreteUnfolded (Datacon.register d, f)
;;
