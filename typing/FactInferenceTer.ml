open Types
open TypeCore

let eq fact1 fact2 =
  assert (fact_leq fact1 fact2);
  assert (fact_leq fact2 fact1)

let analyze_data_types env variables =
  let env1 = FactInference.analyze_data_types env variables
  and env2 = FactInferenceBis.analyze_data_types env variables in
  List.iter (fun v ->
    let fact1 = get_fact env1 v
    and fact2 = get_fact env2 v in
    eq fact1 fact2
  ) variables;
  env1

let analyze_type env ty =
  FactInferenceBis.analyze_type env ty

let is_duplicable env t =
  let d1 = FactInference.is_duplicable env t
  and d2 = FactInferenceBis.is_duplicable env t in
  assert (d1 = d2);
  d1

let is_exclusive env t =
  let d1 = FactInference.is_exclusive env t
  and d2 = FactInferenceBis.is_exclusive env t in
  assert (d1 = d2);
  d1
