open SurfaceSyntax
open UntypedMezzo
module O = UntypedOCaml

(* This is the translation of Untyped Mezzo to Untyped OCaml. *)

(* ---------------------------------------------------------------------------- *)

let datacon_arity (_d : Datacon.name) : int =
  (* not accounting for the hidden adopter field *)
  assert false

let field_index (_d : Datacon.name) (_f : Variable.name) : int =
  (* not accounting for the hidden adopter field *)
  assert false

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

(* OCaml does not have type casts within patterns, so we must produce
   well-typed patterns, and furthermore, if several patterns are
   type-compatible in Mezzo, then their OCaml counterparts must be
   type-compatible in OCaml. *)

(* The translation of [PConstruct] patterns is somewhat tricky. When there
   exist multiple tags (i.e., the pattern is refutable), we must translate it
   to a [PConstruct] pattern, because that is the only way of examining the
   tag within an OCaml pattern. When there exists just one tag, we could
   translate to a [PRecord] pattern; but, for simplicity, we will avoid
   distinguishing a special case. Now, in OCaml, data constructors carry
   anonymous fields, so we are forced to drop the field names and rely purely
   on field offsets. *)

(* For this translation to work, we will have to translate a Mezzo algebraic
   data type to a corresponding OCaml algebraic data type, with the same data
   constructors, same arity (plus one, for the adopter field), and use a
   distinct type variable as the type of each argument. *)

let rec translate_pattern (p : pattern) : O.pattern =
  match p with
  | PVar x ->
      O.PVar (Variable.print x)
  | PTuple ps ->
      O.PTuple (List.map translate_pattern ps)
  | PConstruct (datacon, fields) ->
      (* Build a list of (field index, pattern) pairs. *)
      let fields =
	List.map (fun (f, p) ->
	  (* Add 1 in order to account for the [adopter] field. *)
	  1 + field_index datacon f,
	  translate_pattern p
	) fields
      in
      (* Sort this list by index. *)
      let fields =
	List.sort (fun (i1, _) (i2, _) ->
	  Pervasives.compare i1 i2
	) fields
      in
      (* Complete any missing entries, up to this data constructor's arity,
	 with wildcard patterns. At the same time, forget the indices. *)
      let arity = 1 + datacon_arity datacon in
      let ps = complete 0 arity fields in
      (* Create a data constructor pattern. *)
      O.PConstruct (Datacon.print datacon, ps)
  | PLocated (p, _)
  | PConstraint (p, _) ->
      translate_pattern p
  | PAs (p, x) ->
      O.PAs (translate_pattern p, Variable.print x)
  | PAny ->
      O.PAny

and complete i arity ips =
  if i = arity then
    []
  else
    match ips with
    | (j, p) :: ips when i = j ->
        (* We have an entry at index [i]. Use it. *)
        p :: complete (i + 1) arity ips
    | _ ->
        (* We do not have an entry. Insert a wildcard pattern for this field. *)
        O.PAny :: complete (i + 1) arity ips
