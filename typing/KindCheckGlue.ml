type env =
  TypeCore.var KindCheck.env

(* This function allows building a kind-checking environment out of a
   typing environment. It is quite dirty. I suggest that it would be
   great if we did not need this function. Perhaps a typing environment
   should *contain* a kind-checking environment. Or perhaps the type-checker
   should explicitly maintain both environments. *)

let initial (env : TypeCore.env) : env =
  KindCheck.initial
    (TypeCore.module_name env)
    (TypeCore.get_external_names env)
    (TypeCore.get_external_datacons env)

(* The reason why this function is here is that this allows us to
   avoid a dependency of [KindCheck] on [TypeCore]. *)

