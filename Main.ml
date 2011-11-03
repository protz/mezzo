module DummyTyCon = struct
  type t = string
  let compare = String.compare
  let show tycon = tycon
end

module MD =
  ModeDeduction.Make(Mode)(DummyTyCon)

open Mode
open MD

let atleast cmode =
  OrderingConstraintHypothesis (cmode, ModeVariable)

(* Sample rules. *)

let rules : rule list = [

  (* duplicable int *)
  Rule (0, [ atleast Duplicable ], "int");

  (* forall q, forall a, duplicable <= q /\ q a <-> q (list a) *)
  Rule (1, [ atleast Duplicable; ModeConstraintHypothesis (ModeVariable, 0) ], "list");

  (* exclusive (ref a) *)
  Rule (1, [ atleast Exclusive ], "ref");

]

let context : context =
  List.fold_right add rules empty

(* Sample successful goals. *)

let int =
  TyConApp ("int", [])
let list a =
  TyConApp ("list", [ a ])
let ref a =
  TyConApp ("ref", [ a ])
let alpha =
  TyConApp ("a", [])
let duplicable t =
  ModeConstraintGoal (Duplicable, t)
let exclusive t =
  ModeConstraintGoal (Exclusive, t)
let affine t =
  ModeConstraintGoal (Affine, t)

let successful_goals : goal list = [
  duplicable int;
  affine int;
  duplicable (list int);
  affine (list int);
  affine (ref int);
  affine (ref (list int));
  exclusive (ref (ref (list int)));
  exclusive (ref int);
  exclusive (ref alpha);
  affine (ref alpha);
]

let () =
  List.iter (fun goal ->
    match entails context goal with
    | Yes ->
        ()
    | No _ ->
        assert false (* unexpected failure *)
  ) successful_goals

(* Sample unsuccessful goals. *)

let unsuccessful_goals : goal list = [
  exclusive int;
  exclusive (list int);
  duplicable (ref int);
  duplicable (list (ref int));
  duplicable (list (list (ref (list int))));
  duplicable (list alpha);
  affine (list alpha); (* fails because we do not have the axiom "affine(alpha)" *)
]

let () =
  List.iter (fun goal ->
    match entails context goal with
    | Yes ->
        assert false (* unexpected success *)
    | No explanation ->
        print_newline();
        print_string explanation;
        flush stdout
  ) unsuccessful_goals

