type mode =
  | Duplicable
  | Exclusive
  | Affine

let is_universal = function
  | Duplicable
  | Exclusive ->
      false
  | Affine ->
      true

let leq mode1 mode2 =
  match mode1, mode2 with
  | _, Affine
  | Duplicable, Duplicable
  | Exclusive, Exclusive ->
      true
  | _, _ ->
      false

let show = function
  | Duplicable ->
      "duplicable"
  | Exclusive ->
      "exclusive"
  | Affine ->
      "affine"

