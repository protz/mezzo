(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

let rec split3 = function
  | (x, y, z) :: l ->
      let l1, l2, l3 = split3 l in
      (x :: l1, y :: l2, z :: l3)
  | [] ->
      [], [], []

let ignore_map f l =
  ignore (List.map (fun x -> ignore (f x)) l)

let rec iter3 f l l' l'' =
  match l, l', l'' with
  | hd :: tl, hd' :: tl', hd'' :: tl'' ->
      f hd hd' hd'';
      iter3 f tl tl' tl''
  | [], [], [] ->
      ()
  | _ ->
      raise (Invalid_argument "iter3")

let iter2i f l l' =
  let rec iter2i i f l l' = match l, l' with
    | ([], []) -> ()
    | (e :: rest, e' :: rest') -> f i e e'; iter2i (i + 1) f rest rest'
    | _ -> raise (Invalid_argument "iter2i")
  in
  iter2i 0 f l l'

let rec append_rev_front x y = match x,y with
  | [], l ->
      l
  | x::xs, l ->
      append_rev_front xs (x :: l)

(* Removes duplicates from a list. The default behaviour is to remove identical
 * elements. You can provide your own equality function (and possibly a better
 * hash function) to optimize things or compare elements using a custom
 * criterion. *)
let remove_duplicates (type t') ?(hash_func=Hashtbl.hash) ?(equal_func=(=)) (l: t' list) =
  let module S = struct
    type t = t'
    let equal = equal_func
    let hash = hash_func
  end in
  let module MHT = Hashtbl.Make(S) in
  let seen = MHT.create 16 in
  let l' = ref [] in
  List.iter
    (fun x ->
       if not (MHT.mem seen x) then begin MHT.add seen x (); l' := x :: !l' end
    )
    l;
  !l'

(* Checking for duplicates in a list. [check_for_duplicates compare xs] returns either
   [Some (x1, x2)] where [x1] and [x2] are distinct elements of the list [xs] such
   that [compare x1 x2] is zero, or [None], if no such two elements exist. *)

let check_for_duplicates (compare : 'a -> 'a -> int) (xs : 'a list) : ('a * 'a) option =
  (* Sort the list. *)
  let xs = List.sort compare xs in
  (* Duplicates are now adjacent. *)
  let rec loop x1 = function
    | [] ->
        None
    | x2 :: xs ->
        if compare x1 x2 = 0 then
	  Some (x1, x2)
	else
	  loop x2 xs
  in
  match xs with
  | [] ->
      None
  | x1 :: xs ->
      loop x1 xs

let max l = List.fold_left max min_int l

let filter_some l =
  let l = List.filter (fun x -> x <> None) l in
  List.map Option.extract l

let make i' f =
  let rec make acc i =
    if i = i' then
      List.rev acc
    else
      make ((f i) :: acc) (i + 1)
  in
  make [] 0

let map2i f l1 l2 =
  let rec map2i acc i l1 l2 =
    match l1, l2 with
    | x :: xs, y :: ys ->
        map2i
          ((f i x y) :: acc)
          (i + 1)
          xs
          ys
    | [], [] ->
        List.rev acc
    | _ ->
        raise (Failure "map2i")
  in
  map2i [] 0 l1 l2

let fold_left3 f init l1 l2 l3 =
  let rec fold_left3 acc l1 l2 l3 =
    match l1, l2, l3 with
    | hd1 :: tl1, hd2 :: tl2, hd3 :: tl3 ->
        fold_left3 (f acc hd1 hd2 hd3) tl1 tl2 tl3
    | [], [], [] ->
        acc
    | _ ->
        raise (Invalid_argument "MzList.fold_left3")
  in
  fold_left3 init l1 l2 l3

let fold_left2i f acc l1 l2 =
  let rec fold_left2i i acc l1 l2 =
    match l1, l2 with
    | hd1 :: tl1, hd2 :: tl2 ->
        fold_left2i (i + 1) (f i acc hd1 hd2) tl1 tl2
    | [], [] ->
        acc
    | _ ->
        raise (Invalid_argument "fold_left2i")
  in
  fold_left2i 0 acc l1 l2

let fold_lefti f init l =
  let rec fold_lefti i acc = function
    | hd :: tl ->
        fold_lefti (i + 1) (f i acc hd) tl
    | [] ->
        acc
  in
  fold_lefti 0 init l

let fold_righti f l acc =
  let rec fold_righti i l acc =
    match l with
    | hd :: tl ->
        fold_righti (i + 1) tl (f i hd acc)
    | [] ->
        acc
  in
  fold_righti 0 l acc

let reduce f l =
  List.fold_left f (List.hd l) (List.tl l)

let last l = List.nth l (List.length l - 1)

let nth_opt list index =
  try
    Some (List.nth list index)
  with Not_found ->
    None

let map_some f l =
  filter_some (List.map f l)

let index f l =
  let module M = struct exception Found of int end in
  try
    List.iteri (fun i e' -> if f e' then raise (M.Found i)) l;
    raise Not_found
  with M.Found i ->
    i

let combine3 l1 l2 l3 =
  let rec combine3 acc l1 l2 l3 =
    match l1, l2, l3 with
    | hd1 :: tl1, hd2 :: tl2, hd3 :: tl3 ->
        combine3 ((hd1, hd2, hd3) :: acc) tl1 tl2 tl3
    | [], [], [] ->
        List.rev acc
    | _ ->
        raise (Invalid_argument "combine3")
  in
  combine3 [] l1 l2 l3

let take f l =
  let rec take l l' =
    match l' with
    | [] ->
        None
    | elt :: l' ->
        match f elt with
        | Some result ->
            Some (append_rev_front l l', (elt, result))
        | None ->
            take (elt :: l) l'
  in
  take [] l

let find_opt f l =
  let rec find = function
    | [] ->
        None
    | hd :: tl ->
        match f hd with
        | Some x ->
            Some x
        | None ->
            find tl
  in
  find l

let take_bool f l =
  match take (fun x -> if f x then Some () else None) l with
  | Some (l, (elt, ())) ->
      Some (l, elt)
  | None ->
      None

let map_flatten f l =
  List.flatten (List.map f l)

let cut i l =
  let rec cut acc i l =
    if i = 0 then
      List.rev acc
    else
      match l with
      | hd :: tl ->
          cut (hd :: acc) (i - 1) tl
      | _ ->
          raise (Invalid_argument "cut")
  in
  cut [] i l
