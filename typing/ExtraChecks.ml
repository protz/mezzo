open Types
open TypeErrors

let check_adopts_clauses (env: env): unit =
  fold_types env (fun () point _head { definition; _ } ->
    match definition with
    | Some (Some (_, _, Some clause), _) ->
        if not (FactInference.is_exclusive env clause) then
          raise_error env (
            BadFactForAdoptedType (point, clause, FactInference.analyze_type env clause)
          )
    | _ ->
        ()
  ) ()
;;

let check_env (env: env): unit =
  check_adopts_clauses env
;;
