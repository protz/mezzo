open Types
open TypeErrors

let check_adopts_clauses (env: env): unit =
  let check_fact_exclusive point clause p =
    match get_fact env p with
    | Exclusive ->
        ()
    | _ as f ->
        raise_error env (BadFactForAdoptedType (point, clause, f))
  in
  fold_types env (fun () point _head { definition; _ } ->
    match definition with
    | Some (Some (_, _, Some clause), _) ->
        begin match clause with
        | TyApp _ ->
            let cons, _ = flatten_tyapp clause in
            check_fact_exclusive point clause !!cons
        | TyPoint cons ->
            check_fact_exclusive point clause cons
        | _ ->
            raise_error env (BadTypeForAdopts (point, clause))
        end
    | _ ->
        ()
  ) ()
;;

let check_env (env: env): unit =
  check_adopts_clauses env
;;
