open TypeCore
open Why3

(* ---------------------------------------------------------------------------- *)

(* Why3 specifics *)

type why3env = {
  prover: Whyconf.config_prover;
  driver: Why3.Driver.driver;
  env: Env.env
}

let wenv: why3env option =
  (* Config *)
  let config: Whyconf.config = Whyconf.read_config None in
  let main: Whyconf.main = Whyconf.get_main config in

  try
    (* Prover *)
    let filter_prover: Whyconf.filter_prover =
        Whyconf.mk_filter_prover "alt-ergo" in
    let prover: Whyconf.config_prover =
      Whyconf.filter_one_prover config filter_prover in
    
    (* Driver *)
    let env: Env.env = Env.create_env (Whyconf.loadpath main) in
    let driver: Why3.Driver.driver =
      Why3.Driver.load_driver env prover.Whyconf.driver [] in

    Some {prover; driver; env}

  with _ ->
    None

(* Load the Why3 integer theory which will be used in proofs. *)
let int_theory (wenv: why3env): Theory.theory =
  Env.find_theory wenv.env ["int"] "Int"

(* Build a Why3 task from a given term. *)
let mk_task (wenv: why3env) (t: Term.term): Task.task =
  let task = Task.use_export None (int_theory wenv) in
  let goal_id = Decl.create_prsymbol (Ident.id_fresh "goal") in
  Task.add_prop_decl task Decl.Pgoal goal_id t

(* [why3_check hyps t] returns true if the conjunction of the terms in [hyps]
 * implies the term [t]. *)
let why3_check (hyps: Term.term list) (t: Term.term): bool =
  match wenv with
  | Some wenv ->
      let hyp = List.fold_left Term.t_and Term.t_true hyps in
      let task = mk_task wenv (Term.t_implies hyp t) in
      let result = Call_provers.wait_on_call
        (Why3.Driver.prove_task ~command:wenv.prover.Whyconf.command
        wenv.driver task ()) () in
      begin match result.Call_provers.pr_answer with
      | Call_provers.Valid -> true
      | _ -> false
      end
  | None -> true

let tr_typ (_t: typ): Term.term =
  Term.t_true

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

let implies (hyps: typ list) (consequence: typ): bool =
  let hyps = List.map tr_typ hyps in
  let t = tr_typ consequence in
  why3_check hyps t

let check (env: env) (consequence: typ): bool =
  implies (fetch_arith env) consequence
