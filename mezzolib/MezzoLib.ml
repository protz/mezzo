(* These built-in operations must correspond to those declared in the core
   library (and also implemented by the interpreter). *)

(* ---------------------------------------------------------------------------- *)

(* Because we wish to compile our OCaml code with -nostdlib, we must not
   explicitly depend on the module [Obj]. We copy the required primitive
   types and operations here. *)

(* We rename the type [Obj.t] to our own [MezzoLib.t]. Furthermore, we
   replace [Obj.t] with a type variable in the types of [tag], [set_tag],
   etc. because this allows us to produce code with fewer explicit uses
   of [magic]. *)

type t
external magic : 'a -> 'b = "%identity"
external tag : 'a -> int = "caml_obj_tag"
external set_tag : 'a -> int -> unit = "caml_obj_set_tag"
external field : 'a -> int -> 'b = "%obj_field"
external set_field : 'a -> int -> 'b -> unit = "%obj_set_field"

(* ---------------------------------------------------------------------------- *)

(* Because we wish to compile our OCaml code with -nopervasives, we must not
   explicitly depend on the module [Pervasives]. We copy the required types
   and operations here. *)

let gtz x =
  x > 0

let failwith s =
  Pervasives.failwith s

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

let _mz_print_value v =
  if Obj.is_int v then
    Printf.printf "%d\n" (Obj.magic v : int)
  else
    print_endline "_mz_print_value is not fully implemented."

(* ---------------------------------------------------------------------------- *)

(* Unsafe cast. *)

external _mz_magic : 'a -> 'b = "%identity"

(* ---------------------------------------------------------------------------- *)

(* Arrays. *)

(* A Mezzo array is represented as an OCaml array, whose first slot serves as
   the adopter field. Hence, the length of the OCaml array is one plus the
   length of the Mezzo array. *)

let _mz_array_max_length =
  Sys.max_array_length - 1

let _mz_array_length x =
  Array.length x - 1

let _mz_array_create (n, v) =
  let r = Array.create (1 + n) v in
  r.(0) <- ();
  r

let _mz_array_unsafe_get (r, i) =
  Array.unsafe_get r (1 + i)

let _mz_array_get (r, i) =
  Array.get r (1 + i)

let _mz_array_unsafe_set (r, i, v) =
  Array.unsafe_set r (1 + i) v

let _mz_array_set (r, i, v) =
  Array.set r (1 + i) v

external unsafe_blit : 'a array -> int -> 'a array -> int -> int -> unit = "caml_array_blit"

let _mz_array_unsafe_sub (r, ofs, len) =
  let s = Array.create (1 + len) () in
  unsafe_blit r (1 + ofs) s 1 len;
  s

let _mz_array_append_prim (r1, r2) =
  let n1 = _mz_array_length r1
  and n2 = _mz_array_length r2 in
  let s = Array.create (1 + n1 + n2) () in
  unsafe_blit r1 1 s  1 n1;
  unsafe_blit r2 1 s n1 n2;
  s

let _mz_array_unsafe_blit (r1, ofs1, r2, ofs2, len) =
  unsafe_blit r1 (1 + ofs1) r2 (1 + ofs2) len

