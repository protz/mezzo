type ('x, 'i, 'o) pat =
  'x * 'i

open Obj

let map fx fi _ ((x, i) as p) =
  let x' = fx x in
  let i' = fi i in
  if magic (==) x x' && magic (==) i i' then
    magic p
  else
    x', i'

let fold fx fi fo (x, i) accu =
  let accu = fx x accu in
  let accu = fi i accu in
  accu

