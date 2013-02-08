open SurfaceSyntax
open UntypedMezzo
module O = UntypedOCaml

(* This is the translation of Untyped Mezzo to Untyped OCaml. *)

(* TEMPORARY think about [open]: when we mention a data constructor
   or field name in OCaml, is it always in scope? or must we qualify
   it? can we use qualified names everywhere? *)

(* ---------------------------------------------------------------------------- *)

(* When printing a (variable, type, field) name, we must make sure that it is
   not an OCaml keyword. If it is one, we rename it. *)

let identifier (x : string) =
  if Hashtbl.mem OCamlKeywords.keyword_table x then
    "__ok_" ^ x
  else
    x

(* ---------------------------------------------------------------------------- *)

(* This function maps a field name to a field index. It accounts for the hidden
   adopter field. *)

let field_index (info : datacon_info) (f : Field.name) : int =
  (* TEMPORARY not pretty *)
  (* should we eliminate field names in the earlier pass? *)
  if Field.equal f Mezzo2UntypedMezzo.adopter_field then
    0
  else
    1 + Field.Map.find f info.datacon_fields

(* Sorting a list of pairs of an integer and a datum. *)

let sort_by_index ixs =
  List.sort (fun (i1, _) (i2, _) ->
    Pervasives.compare i1 i2
  ) ixs

(* This function extracts the field index that was provided by the type-checker
   at field access expressions (read and write). This index does not account
   for the hidden adopter field, so we must add 1. *)

let extract_field_index (f : field) : int =
  if Field.equal f.field_name Mezzo2UntypedMezzo.adopter_field then
    0
  else
    match f.field_offset with
    | Some index ->
        1 + index
    | None ->
        (* The field index has not been filled in by the type-checker!? *)
        assert false

(* ---------------------------------------------------------------------------- *)

(* References to data constructors. *)

(* In principle, this reference to a data constructor should be resolved in the
   same way at the OCaml level and at the Mezzo level, so we can print it exactly
   as it appeared in the Mezzo program. *) (* TEMPORARY think about this *)

let print_datacon_reference dref =
  print_maybe_qualified Datacon.print dref.datacon_unresolved

(* ---------------------------------------------------------------------------- *)

(* A few smart constructors. *)

(* As patterns. *)

let pas p x =
  match p with
  | O.PAny ->
      O.PVar x
  | _ ->
      O.PAs (p, x)

(* Integer comparison in OCaml. *)

let apply2 f x y =
  O.EApply (O.EApply (f, x), y)

let gt x y =
  apply2 (O.EVar "Pervasives.(>)") x y

(* Magic. *)

let rec magic e =
  match e with
  | O.EMagic _ ->
      (* Avoid two consecutive magics. *)
      e
  | O.EApply (e1, e2) ->
      (* Push magic into the left-hand side of applications, where it is
	 just as powerful. This will allow more redundancy elimination. *)
      O.EApply (magic e1, e2)
  | e ->
      (* The default case. *)
      O.EMagic e

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
      O.PVar (identifier (Variable.print x))
  | PTuple ps ->
      O.PTuple (List.map translate_pattern ps)
  | PConstruct (dref, fields) ->
      let info : datacon_info = Option.extract dref.datacon_info in
      (* Build a list of (field index, pattern) pairs. *)
      let fields =
	List.map (fun (f, p) ->
	  field_index info f,
	  translate_pattern p
	) fields
      in
      (* Sort this list by index. *)
      let fields = sort_by_index fields in
      (* Complete any missing entries, up to this data constructor's arity,
	 with wildcard patterns. At the same time, forget the indices. *)
      let arity = 1 + info.datacon_arity in
      let ps = complete 0 arity fields in
      (* Create a data constructor pattern. *)
      O.PConstruct (print_datacon_reference dref, ps)
  | PLocated (p, _)
  | PConstraint (p, _) ->
      translate_pattern p
  | PAs (p, x) ->
      pas (translate_pattern p) (identifier (Variable.print x))
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

(* ---------------------------------------------------------------------------- *)

(* Expressions. *)

(* We avoid using [Obj.field] and [Obj.set_field], when possible, because they
   are less efficient in terms of speed and code size. In particular, they seem
   to incorporate a check against the special tag 254, which represents an array
   of values of type double. TEMPORARY not done yet *)

let rec transl (e : expression) : O.expression =
  match e with
  | EVar x ->
      O.EVar (identifier (Variable.print x))
  | EQualified (m, x) ->
      O.EVar (
	Printf.sprintf "%s.%s"
	  (String.capitalize (Module.print m))
	  (identifier (Variable.print x))
      )
  | EBuiltin b ->
      (* The builtin operations are defined in the OCaml library module
	 [MezzoLib]. *)
      O.EVar (Printf.sprintf "MezzoLib.%s" b)
  | ELet (flag, eqs, body) ->
      O.ELet (flag, transl_equations eqs, transl body)
  | EFun (p, e) ->
      O.EFun (translate_pattern p, transl e)
  | EAssign (e1, f, e2) ->
      O.ESetField (magic (transl e1), extract_field_index f, magic (transl e2))
  | EAssignTag (e, dref, info) ->
      (* We must use [Obj.set_tag]; there is no other way. *)
      (* As an optimization, if the old and new integer tags are equal,
	 there is nothing to do. It is OK, in this case, not to translate
         [e] at all, because the definition of Untyped Mezzo guarantees
	 that [e] is a value. *)
      let phantom = Option.extract info.is_phantom_update in
      if phantom then
	O.ETuple []
      else
	let info = Option.extract dref.datacon_info in
	O.ESetTag (transl e, info.datacon_index)
  | EAccess (e, f) ->
      O.EGetField (magic (transl e), extract_field_index f)
  | EApply (e1, e2) ->
      O.EApply (magic (transl e1), transl e2)
  | EMatch (e, branches) ->
      O.EMatch (magic (transl e), transl_branches branches)
  | ETuple es ->
      O.ETuple (List.map transl es)
  | EConstruct (dref, fields) ->
      let info : datacon_info = Option.extract dref.datacon_info in
      (* Build a list of (field index, expression) pairs. *)
      let fields =
	List.map (fun (f, e) ->
	  field_index info f,
	  transl e
	) fields
      in
      (* Sort this list by index. *)
      let fields = sort_by_index fields in
      (* In principle, every field is there. Drop the field names,
	 and create a data constructor expression. *)
      O.EConstruct (print_datacon_reference dref, List.map snd fields)
  | EIfThenElse (e, e1, e2) ->
      O.EIfThenElse (
	gt (O.EGetTag (magic (transl e))) (O.EInt 0),
	transl e1,
	transl e2
      )
  | ESequence (e1, e2) ->
      O.ESequence (transl e1, transl e2)
  | EInt i ->
      O.EInt i
  | EFail s ->
      O.EApply (O.EVar "Pervasives.failwith", O.EStringLiteral s)
  | ENull ->
      (* Using the unit value as a representation of [null]. *)
      O.ETuple []

and transl_equations eqs =
  List.map (fun (p, e) ->
    (* We must insert a [magic] because [e] is matched against [p]. *)
    (* And, if this is a toplevel equation, the bound names of [p]
       will be published at type [Obj.t]. *)
    translate_pattern p, magic (transl e)
  ) eqs

and transl_branches branches =
  List.map (fun (p, e) ->
    (* We insert a [magic] on every branch, because all branches
       must ultimately have the same type. *)
    translate_pattern p, magic (transl e)
  ) branches

(* TEMPORARY if the OCaml inliner is good, an application of a builtin
   function to an argument of the appropriate shape should be simplified
   to an application of the corresponding OCaml primitive operation.
   Check this. If that is not the case, perform this simplification here. *)

(* ---------------------------------------------------------------------------- *)

(* Type variables. *)

let tyvar (i : int) =
  Printf.sprintf "'a%d" i

let ty (i : int) =
  O.TyVar (tyvar i)

let init (n : int) (f : int -> 'a) : 'a list =
  let rec loop (i : int) =
    if i = n then
      []
    else
      let x = f i in
      x :: loop (i + 1)
  in
  loop 0

let tyvars (base : int) (n : int) : string list =
  init n (fun i -> tyvar (base + i))

let tys (base : int) (n : int) : O.ty list =
  init n (fun i -> ty (base + i))

(* ---------------------------------------------------------------------------- *)

(* For each algebraic data type, we create a sum type. *)

let data_sum_name (typecon : Variable.name) : string =
  identifier (Variable.print typecon)

let data_branch ((base : int), (branch : data_type_def_branch)) : O.data_type_def_branch =
  let datacon, fields = branch in
  (* [base] is the base number for numbering our type variables. *)
  let n = List.length fields in
  Datacon.print datacon, tys base n

let data_sum (def : data_type_def) =
  let typecon, branches = def in
  (* We need as many type parameters as there are fields, in total,
     in all branches. *)
  let n = ref 0 in
  let branches =
    List.map (fun ((_, fields) as branch) ->
      let base = !n in
      n := base + List.length fields;
      base, branch
    ) branches
  in
  let n = !n in
  let lhs =
    data_sum_name typecon,
    tyvars 0 n
  in
  let rhs =
    O.Sum (List.map data_branch branches)
  in
  O.DataTypeGroup (lhs, rhs)

(* ---------------------------------------------------------------------------- *)

(* Translating top-level items. *)

let translate_item = function
  | DataType def ->
      [ data_sum def ]
  | ValueDefinition (flag, eqs) ->
      [ O.ValueDefinition (flag, transl_equations eqs) ]
  | ValueDeclaration x ->
      [ O.ValueDeclaration (Variable.print x, O.TyVar "Obj.t") ]
  | OpenDirective m ->
      [ O.OpenDirective (String.capitalize (Module.print m)) ]

(* ---------------------------------------------------------------------------- *)

(* Translating implementations. *)

let translate_implementation items =
  List.flatten (List.map translate_item items)

