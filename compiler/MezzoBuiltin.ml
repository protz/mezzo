(* These built-in operations must correspond to those declared in the core
   library (and also implemented by the interpreter). *)

(* ---------------------------------------------------------------------------- *)

(* For the moment, a Mezzo Boolean value is not the same thing as an OCaml
   Boolean value. Hence, the following conversion is required. TEMPORARY *)

type __mz_fake_bool =
  | MzFalse__ of Obj.t
  | MzTrue__ of Obj.t

let __mz_False =
  MzFalse__ (Obj.repr ())

let __mz_True =
  MzTrue__ (Obj.repr ())

let __mz_fake_bool (b : bool) : __mz_fake_bool =
  if b then __mz_True else __mz_False

(* ---------------------------------------------------------------------------- *)

(* Arithmetic. *)

let _mz_iadd (i1, i2) =
  i1 + i2

let _mz_isub (i1, i2) =
  i1 - i2

let _mz_imul (i1, i2) =
  i1 * i2

let _mz_idiv (i1, i2) =
  if i2 = 0 then
    (* Mezzo does not have exceptions! *)
    0
  else
    i1 / i2

let _mz_ieq ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 = i2)

let _mz_ine ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 <> i2)

let _mz_ilt ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 < i2)

let _mz_ile ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 <= i2)

let _mz_igt ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 > i2)

let _mz_ige ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 >= i2)

let _mz_ige ((i1, i2) : (int * int)) =
  __mz_fake_bool (i1 >= i2)

let _mz_iand (i1, i2) =
  i1 land i2

(* ---------------------------------------------------------------------------- *)

(* Address comparison. *)

let _mz_address_eq (x, y) =
  __mz_fake_bool (x == y)

(* ---------------------------------------------------------------------------- *)

(* The polymorphic [print] operation. *)

(* We could implement something, although the output would differ from the
   interpreter's. TEMPORARY *)

let _mz_print_value _ =
  print_endline "_mz_print_value is not implemented."

(* ---------------------------------------------------------------------------- *)

(* Unsafe cast. *)

let _mz_magic v =
  v

