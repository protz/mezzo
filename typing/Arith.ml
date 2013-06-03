open TypeCore
open Why3

module StringMap = Map.Make (String)

(* ---------------------------------------------------------------------------- *)

(* Why3 specifics *)

type why3env = {
  prover: Whyconf.config_prover;
  driver: Why3.Driver.driver;
  env: Env.env;
  int_theory: Theory.theory;
  symbols: Term.lsymbol StringMap.t; 
  minus: Term.term -> Term.term;
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
    
    (* Int theory *)
    let int_theory: Theory.theory =
      Env.find_theory env ["int"] "Int" in
    (* Some symbols *)
    let symbols: Term.lsymbol StringMap.t =
      List.fold_left (fun m s ->
        StringMap.add ("~"^s) (
          Theory.ns_find_ls int_theory.Theory.th_export ["infix " ^ s]
        ) m
      ) StringMap.empty [">";"<";">=";"<=";"=";"-";"+"] in
    (* The minus operator is used to build negative integers. *)
    let minus t = 
      let minus = StringMap.find "-" symbols in
      let zero = Term.t_nat_const 0 in
      Term.t_app_infer minus [zero; t]
    in

    Some {prover; driver; env; int_theory; symbols; minus}

  with _ ->
    None

(* ---------------------------------------------------------------------------- *)

(* A few auxiliaries. *)
    
(* Build a Why3 task from a given term. *)
let mk_task (wenv: why3env) (t: Term.term): Task.task =
  let task = Task.use_export None wenv.int_theory in
  let goal_id = Decl.create_prsymbol (Ident.id_fresh "goal") in
  Task.add_prop_decl task Decl.Pgoal goal_id t

(* TEMPORARY The way we distinguish an arithmetic operator from other functions
 * should change later. *)
let get_symbol (env: env) (var: var): string =
  let var = get_name env var in
  let var = Resugar.surface_print_var env var in
  Variable.print (SurfaceSyntax.unqualify var)

let is_arith_op (env: env) (var: var): bool =
  (* TEMPORARY Check with first character if the function is arithmetic. *)
  String.get (get_symbol env var) 0 = '~'

(* Creates a new Term.vsymbol with a name taken from var. *)
let mk_vsymbol (env: env) (var: var): Term.vsymbol =
  let name = get_symbol env var in
  let ident = Ident.id_fresh name in
  let vsymbol = Term.create_vsymbol ident Ty.ty_int in
  vsymbol

(* Translates an integer to a Term.term. *)
let mk_int (wenv: why3env) (i: int): Term.term =
  if i >= 0 then Term.t_nat_const i
  else wenv.minus (Term.t_nat_const (-i))

(* ---------------------------------------------------------------------------- *)

exception Flexible

(* This is a functor because we have to create a VarMap whose equality between
 * keys depends on a give [env]. *)

module ArithChecker (E: sig val wenv: why3env val env: env end) = struct
  
  let wenv = E.wenv
  let env = E.env
  
  module VarMap = VarMapModulo(struct let env = env end)
  type symbolMap = Term.vsymbol VarMap.t

  (* [why3_check hyps t] returns true if the conjunction of the terms in [hyps]
   * implies the term [t]. *)
  let why3_check (vars: symbolMap) (hyps: Term.term list) (t: Term.term): bool =
    (* Build the term. *)
    let hyp = List.fold_left Term.t_and Term.t_true hyps in
    let t = Term.t_implies hyp t in
    let t = Term.t_forall_close (List.map snd (VarMap.to_list vars)) [] t in
    (*Format.printf "%a\n" Pretty.print_term t;*)
    (* Build the task. *)
    let task = mk_task wenv t in
    (* Call the prover. *)
    let result = Call_provers.wait_on_call
      (Why3.Driver.prove_task ~command:wenv.prover.Whyconf.command
      wenv.driver task ()) () in
    (* Evaluate the answer. *)
    match result.Call_provers.pr_answer with
    | Call_provers.Valid -> true
    | _ -> false
  
  (* [tr_typ vars t] translates the type [t] into a Why3 term. It takes
   * into account the already translated variables in [vars]. *)
  let rec tr_typ (vars: symbolMap) (t: typ):
    symbolMap * Term.term =
    match modulo_flex env t with
    | TyApp (TyOpen op, args) ->
        (* Translate the operands *)
        let vars, l = tr_many vars args in
        (* Apply the right operator *)
        vars, Term.t_app_infer (StringMap.find (get_symbol env op) wenv.symbols) l
    | TyLiteral i -> vars, mk_int wenv i
    | TyOpen var ->
        if is_flexible env var then raise Flexible;
        begin try
          (* We already saw this variable *)
          vars, Term.t_var (VarMap.find var vars)
        with Not_found ->
          (* New variable *)
          let symbol = mk_vsymbol env var in 
          let new_map = VarMap.add var symbol vars in
          new_map, Term.t_var symbol
        end
    | _ -> assert false
  
  (* [tr_many vars l] is basically the folding of [l] with [tr_typ]. *)
  and tr_many  (vars: symbolMap) (l: typ list):
    symbolMap * Term.term list =
    match l with
    | [] -> vars, []
    | hd :: tl ->
        (* Update the [symbolMap] when calling [tr_typ] or [tr_many]. *)
        let vars, t = tr_typ vars hd in
        let vars, tl = tr_many vars tl in
        vars, t :: tl
  
  (* [implies wenv hyps consequence] wraps the above functions to verify that
   * [consequence] is implied by [hyps]. *)
  let implies (hyps: typ list) (consequence: typ): bool =
    let vars = VarMap.empty in
    let vars, t = tr_typ vars consequence in
    let vars, hyps = tr_many vars hyps in
    why3_check vars hyps t

end

let fetch_arith (env: env): typ list =
  (* An arithmetic permission is a TyApp whose function is arithmetic. *)
  List.filter (function
    | TyApp (TyOpen v, _) -> is_arith_op env v
    | _ -> false
  ) (get_floating_permissions env)


let check (env: env) (consequence: typ): bool =
  match wenv with
  | Some wenv -> (
    try
      let module A = ArithChecker(struct let wenv = wenv let env = env end) in
      A.implies(fetch_arith env) consequence
    with Flexible -> false)
  | None ->
      (* Why3 isn't available, accept all arithmetic check. *)
      true
