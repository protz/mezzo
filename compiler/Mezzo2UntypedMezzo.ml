open SurfaceSyntax
module U = UntypedMezzo

(* ---------------------------------------------------------------------------- *)

(* The adopter field. *)

(* This field is special in that it is present in every data constructor
   declaration, and is always at offset 0. Furthermore, we must be able
   to access this field without knowing with which data constructor it is
   associated. Thus, we produce a dummy data constructor definition, which
   carries just this field, and use it when compiling accesses to the
   adopter field. *)

let adopter_field_name =
  Variable.register "__mz_adopter"

let adopter_datacon =
  Datacon.register "MezzoAdopter__"

let adopter_field = {
  field_name = adopter_field_name;
  field_datacon = adopter_datacon;
}

let init_adopter_field fields =
  (adopter_field_name, U.ENull) :: fields

(* ---------------------------------------------------------------------------- *)

(* A cosmetic optimization: eliminate sequences whose left-hand side is a unit
   value. *)

let rec is_unit = function
  | ETuple []
  | EAssert _ ->
      true
  | ELocated (e, _)
  | EConstraint (e, _) ->
      is_unit e
  | _ ->
      false

(* ---------------------------------------------------------------------------- *)

(* Code generation for the dynamic test at abandon. *)

let abandon x1 x2 success failure =
  let open U in
  (* if x1.adopter == x2 *)
  EIfThenElse (
    EApply (
      EBuiltin "_mz_address_eq",
      ETuple [
	EAccess (EVar x1, adopter_field);
	EVar x2
      ]
    ),
    success,
    failure
  )

(* ---------------------------------------------------------------------------- *)

(* The Boolean values are [core::True] and [core::False]. *)

(* TEMPORARY The syntax of (Untyped) Mezzo currently does not support qualified
   data constructors, so we cheat by masquerading them as variables. *)

let core =
  Module.register "core"

let f =
  U.EQualified (core, Variable.register "False")

let t =
  U.EQualified (core, Variable.register "True")

(* ---------------------------------------------------------------------------- *)

(* Expressions. *)

let rec translate_expression (loc : location) (e : expression) : U.expression =
  match e with
  | EConstraint (e, _) ->
      translate_expression loc e
  | EVar x ->
      U.EVar x
  | EQualified (m, x) ->
      U.EQualified (m, x)
  | EBuiltin b ->
      U.EBuiltin b
  | ELet (flag, equations, body) ->
      U.ELet (flag, translate_equations loc equations, translate_expression loc body)
  | EFun (_type_parameters, argument_type, _result_type, body) ->
      (* The argument pattern is implicit in the argument type. *)
      let p = type_to_pattern argument_type in
      U.EFun (p, translate_expression loc body)
  | EAssign (e1, f, e2) ->
      U.EAssign (translate_expression loc e1, f, translate_expression loc e2)
  | EAssignTag (e, tags) ->
      U.EAssignTag (translate_expression loc e, tags)
  | EAccess (e, f) ->
      U.EAccess (translate_expression loc e, f)
  | EAssert _ ->
      U.ETuple []
  | EApply (e1, e2) ->
      U.EApply (translate_expression loc e1, translate_expression loc e2)
  | ETApply (e, _) ->
      translate_expression loc e
  | EMatch (_, e, branches) ->
      U.EMatch (translate_expression loc e, translate_equations loc branches)
  | ETuple es ->
      U.ETuple (List.map (translate_expression loc) es)
  | EConstruct (datacon, fes) ->
      (* Introduce the adopter field. *)
      U.EConstruct (
	datacon,
	init_adopter_field (translate_fields loc fes)
      )
  | EIfThenElse (_, e, e1, e2) ->
      U.EIfThenElse (translate_expression loc e, translate_expression loc e1, translate_expression loc e2)
  | ESequence (e1, e2) ->
      if is_unit e1 then
	translate_expression loc e2
      else
	U.ESequence (translate_expression loc e1, translate_expression loc e2)
  | ELocated (e, loc) ->
      translate_expression loc e
  | EInt i ->
      U.EInt i
  | EExplained e ->
      translate_expression loc e

  (* Compilation of adoption and abandon: [give], [take], and [owns]. *)

  (* In each case, we must first convert to A-normal form, i.e. introduce
     auxiliary variables if necessary. *)

  | EGive (e1, e2) ->
      U.EAssign (translate_expression loc e1, adopter_field, translate_expression loc e2)

  | ETake (EVar x1, EVar x2) ->
      let open U in
      (* if x1.adopter == x2 *)
      abandon x1 x2
	(* then x1.adopter <- null *)
	(EAssign (EVar x1, adopter_field, ENull))
	(* else fail *)
	(EFail (Log.msg "%a\nA take instruction failed.\n" Lexer.p loc))

  | ETake (EVar x1, e2) ->
      let eval_e2, v2 = ParserUtils.name "adopter" e2 in
      translate_expression loc (eval_e2 (ETake (EVar x1, v2)))

  | ETake (e1, e2) ->
      let eval_e1, v1 = ParserUtils.name "adoptee" e1 in
      translate_expression loc (eval_e1 (ETake (v1, e2)))

  | EOwns (EVar x2, EVar x1) ->
      (* if x1.adopter == x2 *)
      abandon x1 x2
	(* then True *)
	t
	(* else False *)
	f

  | EFail ->
      U.EFail (Log.msg "%a\nA fail instruction was encountered.\n" Lexer.p loc)

and translate_equations loc equations =
  List.map (fun (p, e) ->
    p, translate_expression loc e
  ) equations

and translate_fields loc fields =
  List.map (fun (f, e) ->
    f, translate_expression loc e
  ) fields

(* TEMPORARY when translating to ocaml, make sure to impose left-to-right
   evaluation order *)

(* TEMPORARY experiments show that Obj.field and Obj.set_field are less
   efficient than ordinary field accesses, because they contain a test
   for the special tag 254 (array of doubles). Furthermore, an ordinary
   field write instruction is more efficient when the value is known to
   be an integer, because there is no write barrier in that case. Could
   the Mezzo type-checker provide us with this information? *)

(* TEMPORARY could optimize [take] when preceded with an [owns] test *)
(* TEMPORARY could also optimize [if x1 owns x2 then ...] *)

(* TEMPORARY when translating a variable to ocaml, should make sure it
   is not an ocaml keyword *)

