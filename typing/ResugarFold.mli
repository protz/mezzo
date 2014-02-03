open TypeCore

(** This is only for display purposes. *)
val fold_type : env -> typ -> typ option
val fold_var : env -> var -> typ option
