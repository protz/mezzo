open TypeCore
open Why3

(* ---------------------------------------------------------------------------- *)

(* Why3 specifics *)

type _why3env = {
  prover: Whyconf.config_prover;
  driver: Why3.Driver.driver;
  env: Env.env
}

(* ---------------------------------------------------------------------------- *)

(* Public interface *)

(* TEMPORARY The way we distinguish an arithmetic operator from other functions
 * should change later. *)
let is_arith_op (env: env) (var: var): bool =
  let var = get_name env var in
  let var = Resugar.surface_print_var env var in
  let var = SurfaceSyntax.print_maybe_qualified Variable.print var in
  (* TEMPORARY Check with first characters if the function is arithmetic. *)
  String.length var > 8 && String.sub var 0 8 = "arith::~"

let fetch_arith (env: env): typ list =
  (* An arithmetic permission is a TyApp whose function is aarithmetic. *)
  List.filter (function
    | TyApp (TyOpen v, _) -> is_arith_op env v
    | _ -> false
  ) (get_floating_permissions env)

let implies (_hyps: typ list) (_consequence: typ): bool =
  true

let check (env: env) (consequence: typ): bool =
  implies (fetch_arith env) consequence
