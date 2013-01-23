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

open SurfaceSyntax

(* This is the Mezzo interpreter. *)

(* ---------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------- *)

(* The interpreter treats data constructor definitions as generative. That is,
   the evaluation of a data constructor definition causes the generation of a
   fresh information record, to which the data constructor becomes bound. (This
   information record could in principle contain a unique identifier; it
   doesn't, because we don't need it.) Data constructors are treated just like
   variables: i.e., they are bound in the environment. This implies, for
   instance, that if a function refers to a data constructor, then this data
   constructor is interpreted in the closure's environment. We adopt this
   approach because it seems simple, efficient, and deals correctly with
   masking. *)

(* We maintain the following information about every data constructor. *)

type datacon_info = {
  (* Its unqualified name (used only by [print_value]). *)
  datacon_name: string;
  (* Its arity (i.e., number of fields). *)
  datacon_arity: int;
  (* Its integer index within its data type definition. *)
  datacon_index: int;
  (* A map of field names to field indices. *)
  datacon_fields: int Variable.Map.t;
}

(* ---------------------------------------------------------------------------- *)

(* Thus, we have two namespaces: variables and data constructors. *)

module V =
  InterpreterNamespace.MakeNamespace(Variable)

module D =
  InterpreterNamespace.MakeNamespace(Datacon)

(* ---------------------------------------------------------------------------- *)

(* An environment contains the following information: *)

type env = {
    (* A map of (unqualified or qualified) variables to values. *)
    variables: value V.global_env;
    (* A map of (unqualified) data constructors to data constructor information. *)
    datacons: datacon_info D.global_env;
}

(* ---------------------------------------------------------------------------- *)

(* A value is one of the following: *)

and value =
    (* A primitive integer value. *)
  | VInt of int
    (* The address of a memory block. *)
  | VAddress of block
    (* A tuple. *)
  | VTuple of value list
    (* A closure. *)
  | VClosure of closure
    (* A built-in function. *)
  | VBuiltin of string

(* A memory block contains the following information: *)

and block = {
  (* A data constructor, represented by its [datacon_info] record.
     We cannot work with just the [datacon_index], because we must
     be able to disambiguate field accesses, i.e., translate a field
     name to an offset. *)
  mutable tag: datacon_info;
  (* An adopter pointer, which is either null or the address of some other block. *)
  mutable adopter: block option;
  (* A set of fields. *)
  fields: value (* mutable *) array;
}

(* A closure contains the following information: *)

and closure = {
  (* The function's formal argument, a pattern. *)
  arg: pattern;
  (* The function's body, an expression. *)
  body: expression;
  (* The environment. *)
  (* This field is mutable only in order to allow initializing
     a recursive closure (this is Landin's knot). *)
  mutable env: env;
}

(* ---------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------- *)

(* An empty interpreter environment. *)

let empty : env = {
  variables = V.empty;
  datacons = D.empty;
}

(* Extending the environment with a new unqualified variable. *)

let extend_unqualified_variable x v env =
  { env with variables = V.extend_unqualified x v env.variables }

(* Extending the environment with a new unqualified data constructor. *)

let extend_unqualified_datacon x info env =
  { env with datacons = D.extend_unqualified x info env.datacons }

(* Opening a module. *)

let unqualify m env =
  {
    variables = V.unqualify m env.variables;
    datacons = D.unqualify m env.datacons;
  }

(* Removing all unqualified bindings. *)

let zap env =
  {
    variables = V.zap env.variables;
    datacons = D.zap env.datacons;
  }

(* ---------------------------------------------------------------------------- *)

(* Constant value definitions. *)

(* The unit value is the empty tuple. *)

let unit_value =
  VTuple []

(* The Boolean values are [core::True] and [core::False]. Unfortunately, these
   are not constants, because we need to find the [datacon_info] records
   associated with these data constructors. (If required, we could fake them,
   but let's not bother. This is not performance-critical anyway: these Boolean
   values are produced only by the evaluation of [EOwn].) *)

let core =
  Module.register "core"

let f =
  Datacon.register "False"

let t =
  Datacon.register "True"

let false_value (env : env) =
  (* We assume that the module [core] has been loaded at this point. *)
  let info = D.lookup_qualified core f env.datacons in
  VAddress { tag = info; adopter = None; fields = [||] }

let true_value (env : env) =
  let info = D.lookup_qualified core t env.datacons in
  VAddress { tag = info; adopter = None; fields = [||] }

let bool (env : env) (b : bool) =
  if b then true_value env else false_value env

(* ---------------------------------------------------------------------------- *)

(* A pretty-printer for values. *)

module ValuePrinter = struct

  open Hml_Pprint

  let parens content =
    group (lparen ^^ nest 2 (break0 ^^ content) ^^ break0 ^^ rparen)

  let braces content =
    group (lbrace ^^ nest 2 (break1 ^^ content) ^^ break1 ^^ rbrace)

  (* The [depth] parameter is incremented at every memory block, and
     we stop when it reaches a hard-coded limit. This prevents entering
     an infinite loop when the heap is cyclic. It also helps visualize
     huge values. *)

  let rec print_value (env : env) (depth : int) (v : value) : document =
    if depth >= 5 then
      text "..."
    else
      match v with
      | VInt i ->
	  text (string_of_int i)
      | VAddress b ->
	  let info = b.tag in
	  let fields : (int * string * value) list =
	    Variable.Map.fold (fun field index accu ->
	      (index, Variable.print field, b.fields.(index)) :: accu
	    ) info.datacon_fields []
	  in
	  let fields =
	    List.sort (fun (i1, _, _) (i2, _, _) ->
	      Pervasives.compare i1 i2
	    ) fields
	  in
	  begin match fields with
	  | [] ->
	      text info.datacon_name
	  | _ :: _ ->
	      group (
		text info.datacon_name ^^ space ^^ braces (
		  join (semi ^^ break1) (List.map (fun (_, field, v) ->
		    group (
		      text field ^^
		      space ^^ equals ^^ nest 2 (break1 ^^
			print_value env (depth + 1) v
		      )
		    )
		  ) fields)
		)
	      )
	  end
      | VTuple vs ->
	  parens (
	    join (comma ^^ break1) (List.map (print_value env depth) vs)
	  )
      | VClosure _
      | VBuiltin _ ->
	  text "<fun>"

  let render env v : string =
    render (print_value env 0 v)

end

(* ---------------------------------------------------------------------------- *)

(* Un-tagging values. *)

let asInt (v : value) : int =
  match v with
  | VInt i ->
      i
  | _ ->
      (* Runtime tag error. *)
      assert false

let asBlock (v : value) : block =
  match v with
  | VAddress block ->
      block
  | _ ->
      (* Runtime tag error. *)
      assert false

let asTuple (v : value) : value list =
  match v with
  | VTuple vs ->
      vs
  | _ ->
      (* Runtime tag error. *)
      assert false

let asPair (v : value) : value * value =
  match asTuple v with
  | [ v1; v2 ] ->
      v1, v2
  | _ ->
      (* Runtime arity error. *)
      assert false

let asIntPair (v : value) : int * int =
  let v1, v2 = asPair v in
  asInt v1, asInt v2

(* ---------------------------------------------------------------------------- *)

(* Evaluating an application of a built-in function. *)

let eval_builtin (env : env) (b : string) (v : value) : value =
  match b with
  | "_mz_iadd" ->
      let i1, i2 = asIntPair v in
      VInt (i1 + i2)
  | "_mz_isub" ->
      let i1, i2 = asIntPair v in
      VInt (i1 - i2)
  | "_mz_imul" ->
      let i1, i2 = asIntPair v in
      VInt (i1 * i2)
  | "_mz_idiv" ->
      let i1, i2 = asIntPair v in
      VInt (i1 / i2)
  | "_mz_ieq" ->
      let i1, i2 = asIntPair v in
      bool env (i1 = i2)
  | "_mz_ine" ->
      let i1, i2 = asIntPair v in
      bool env (i1 <> i2)
  | "_mz_ilt" ->
      let i1, i2 = asIntPair v in
      bool env (i1 < i2)
  | "_mz_ile" ->
      let i1, i2 = asIntPair v in
      bool env (i1 <= i2)
  | "_mz_igt" ->
      let i1, i2 = asIntPair v in
      bool env (i1 > i2)
  | "_mz_ige" ->
      let i1, i2 = asIntPair v in
      bool env (i1 >= i2)
  | "_mz_iand" ->
      let i1, i2 = asIntPair v in
      VInt (i1 land i2)
  | "_mz_address_eq" ->
      let v1, v2 = asPair v in
      let b1 = asBlock v1
      and b2 = asBlock v2 in
      bool env (b1 == b2)
      (* TEMPORARY should be a rich_bool, not a bool *)
  | "_mz_print_value" ->
      print_endline (ValuePrinter.render env v);
      unit_value
  | _ ->
      Log.error "Unknown builtin function: %s\n" b

(* ---------------------------------------------------------------------------- *)

(* Exploiting information about data constructors. *)

(* Finding a field in a table. *)

let find_field (f : Variable.name) (fields : 'a Variable.Map.t) : 'a =
  try
    Variable.Map.find f fields
  with Not_found ->
    (* Unknown field. *)
    assert false

(* Translating a data-constructor-and-field pair to an integer offset. *)

let field_offset (f : Variable.name) (info : datacon_info) : int =
  find_field f info.datacon_fields

(* ---------------------------------------------------------------------------- *)

(* Translating a type to a pattern. *)

let rec type_to_pattern (ty : typ) : pattern =
  match ty with

  (* A structural type constructor is translated to the corresponding
     structural pattern. *)

  | TyTuple tys ->
      PTuple (List.map type_to_pattern tys)

  | TyConcreteUnfolded (datacon, fields) ->
      let fps =
	List.fold_left (fun fps field ->
	  match field with
          | FieldValue (f, ty) -> (f, type_to_pattern ty) :: fps
          | FieldPermission _  -> fps
	) [] fields in
      PConstruct (datacon, fps)

   (* A name introduction gives rise to a variable pattern. *)

  | TyNameIntro (x, ty) ->
      PAs (type_to_pattern ty, PVar x)

  (* Pass (go down into) the following constructs. *)

  | TyLocated (ty, _)
  | TyAnd (_, ty)
  | TyConsumes ty
  | TyBar (ty, _) ->
      type_to_pattern ty

  (* Stop at (do not go down into) the following constructs. *)

  | TyForall _
  | TyUnknown
  | TyArrow _ 
  | TySingleton _
  | TyQualified _
  | TyDynamic
  | TyApp _
  | TyVar _ ->
      PAny

  (* The following cases should not arise. *)

  | TyEmpty
  | TyStar _
  | TyAnchoredPermission _ ->
      (* Type of kind PERM, where a type of kind TERM was expected. *)
      assert false

(* ---------------------------------------------------------------------------- *)

(* Matching a value [v] against a pattern [p]. The resulting bindings are
   accumulated in the environment [env]. *)

(* The data constructors that appear in the pattern [p] are interpreted
   using the same environment [env] that serves as an accumulator. This
   may seem slightly dirty, but is ok: [env] serves an accumulator for
   variable bindings, so as far as data constructor bindings are concerned,
   it remains unchanged as we progress through the matching process. *)

(* The main function, [match_pattern], raises [MatchFailure] if [p] does not
   match [v]. The following two functions, [match_irrefutable_pattern] and
   [match_refutable_pattern], catch this exception. *)

exception MatchFailure

let rec match_pattern (env : env) (p : pattern) (v : value) : env =
  match p with
  | PVar x ->
      extend_unqualified_variable x v env
  | PTuple ps ->
      begin try
	List.fold_left2 match_pattern env ps (asTuple v)
      with Invalid_argument _ ->
	(* Tuples of non-matching lengths. *)
	assert false
      end
  | PConstruct (datacon, fps) ->
      let b = asBlock v in
      let info = D.lookup_unqualified datacon env.datacons in
      if info == b.tag then
	let fields = b.fields in
        List.fold_left (fun env (f, p) ->
	  let offset = find_field f info.datacon_fields in
	  match_pattern env p fields.(offset)
	) env fps
      else begin
	(* A sanity check: physical equality of [datacon_info] records
	   should be equivalent to equality of the [datacon_index] fields. *)
	assert (info.datacon_index <> b.tag.datacon_index);
        raise MatchFailure
      end
  | PLocated (p, _)
  | PConstraint (p, _) ->
      match_pattern env p v
  | PAs (p1, p2) ->
      let env = match_pattern env p1 v in
      let env = match_pattern env p2 v in
      env
  | PAny ->
      env

let match_irrefutable_pattern (env : env) (p : pattern) (v : value) : env =
  try
    match_pattern env p v
  with MatchFailure ->
    (* This pattern was supposed to be irrefutable! *)
    assert false

let match_refutable_pattern (env : env) (p : pattern) (v : value) : env option =
  try
    Some (match_pattern env p v)
  with MatchFailure ->
    None

(* ---------------------------------------------------------------------------- *)

(* Evaluating an expression. *)

let rec eval (env : env) (e : expression) : value =
  match e with

  | EConstraint (e, _) ->
      eval env e

  | EVar x ->
      V.lookup_unqualified x env.variables

  | EQualified (m, x) ->
      V.lookup_qualified m x env.variables

  | EBuiltin b ->
      VBuiltin b

  | ELet (rec_flag, equations, body) ->
      let env = eval_value_definition env (DMultiple (rec_flag, equations)) in
      eval env body

  | EFun (_type_parameters, argument_type, _result_type, body) ->
      VClosure {
	(* The argument pattern is implicit in the argument type. *)
	arg = type_to_pattern argument_type;
	(* The function body. *)
	body = body;
	(* The environment. *)
	(* TEMPORARY environment could/should be filtered? *)
	env = env;
      }

  | EAssign (e1, { field_name = f; _ }, e2) ->
      (* We do not assume that the type-checker has annotated the abstract
	 syntax tree, so we cannot use the field [field_datacon]. Instead,
         we rely on the fact that [b1.tag] is a [datacon_info] record and
         contains a mapping of field names to field offsets. *)
      let b1 = asBlock (eval env e1) in
      let v2 = eval env e2 in
      b1.fields.(field_offset f b1.tag) <- v2;
      unit_value

  | EAssignTag (e, { new_datacon; _ }) ->
      (* We do not assume that the type-checker has annotated the abstract
	 syntax tree, so we cannot use the field [previous_datacon]. *)
      let b = asBlock (eval env e) in
      b.tag <- D.lookup_unqualified new_datacon env.datacons;
      unit_value

  | EAccess (e, { field_name = f; _ }) ->
      (* We do not assume that the type-checker has annotated the abstract
	 syntax tree, so we cannot use the field [field_datacon]. Instead,
         we rely on the fact that [b.tag] is a [datacon_info] record and
         contains a mapping of field names to field offsets. *)
      let b = asBlock (eval env e) in
      b.fields.(field_offset f b.tag)

  | EAssert _ ->
      unit_value

  | EApply (e1, e2) ->
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      begin match v1 with
      | VClosure c1 ->
	  (* Extend the closure's environment with a binding of the
	     formal argument to the actual argument. Evaluate the
	     closure body. *)
	  eval (match_irrefutable_pattern c1.env c1.arg v2) c1.body
      | VBuiltin b ->
	  eval_builtin env b v2
      | _ ->
	  (* Runtime tag error. *)
	  assert false
      end

  | ETApply (e, _) ->
      eval env e

  | EMatch (_, e, branches) ->
      switch env (eval env e) branches

  | ETuple es ->
      (* [List.map] implements left-to-right evaluation. *)
      VTuple (List.map (eval env) es)

  | EConstruct (datacon, fes) ->
      (* Evaluate the fields in the order specified by the programmer. *)
      let fvs =
	List.map (fun (f, e) -> (f, eval env e)) fes
      in
      (* Allocate a field array. *)
      let info = D.lookup_unqualified datacon env.datacons in
      let fields = Array.create info.datacon_arity unit_value in
      (* Populate the field array. *)
      List.iter (fun (f, v) ->
	let offset = find_field f info.datacon_fields in
	fields.(offset) <- v
      ) fvs;
      (* Allocate a memory block. *)
      VAddress {
	tag = info;
	adopter = None;
	fields = fields;
      }

  | EIfThenElse (_, e, e1, e2) ->
      let b = asBlock (eval env e) in
      eval env (if b.tag.datacon_index > 0 then e1 else e2)

  | ESequence (e1, e2) ->
      let _unit = eval env e1 in
      eval env e2

  | ELocated (e, _) ->
      (* TEMPORARY keep track of locations for runtime error messages *)
      eval env e

  | EInt i ->
      VInt i

  | EExplained e ->
      eval env e

  | EGive (e1, e2) ->
      let b1 = asBlock (eval env e1) in
      let b2 = asBlock (eval env e2) in
      assert (b1.adopter = None);
      b1.adopter <- Some b2;
      unit_value

  | ETake (e1, e2) ->
      let b1 = asBlock (eval env e1) in
      let b2 = asBlock (eval env e2) in
      begin match b1.adopter with
      | Some b when (b == b2) ->
          b1.adopter <- None;
          unit_value
      | _ ->
          Log.error "Take failure.\n"
      end

  | EOwns (e1, e2) ->
      let b1 = asBlock (eval env e1) in
      let b2 = asBlock (eval env e2) in
      begin match b1.adopter with
      | Some b when (b == b2) ->
	  true_value env
      | _ ->
          false_value env
      end

  | EFail ->
      Log.error "Failure.\n"

(* ---------------------------------------------------------------------------- *)

(* Evaluating a switch construct. *)

and switch (env : env) (v : value) (branches : (pattern * expression) list) : value =
  match branches with
  | (p, e) :: branches ->
      begin match match_refutable_pattern env p v with
      | Some env ->
	  (* [p] matches [v]. Evaluate the branch [e]. *)
	  eval env e
      | None ->
	  (* [p] does not match [v]. Try the next branch. *)
	  switch env v branches
      end
  | [] ->
      (* No more branches. This should not happen if the type-checker has
         checked for exhaustiveness. At the moment, this is not done,
         though. *)
      (* TEMPORARY should print a location and the value [v] *)
      Log.error "Match failure.\n"

(* ---------------------------------------------------------------------------- *)

(* Evaluating a value definition. *)

and eval_value_definition (env : env) (def : declaration) : env =
  match def with
  | DLocated (def, _, _) ->
      eval_value_definition env def

  | DMultiple (Nonrecursive, equations) ->
      (* Evaluate the equations, in left-to-right order. *)
      List.fold_left (fun new_env (p, e) ->
	(* For each equation [p = e], evaluate the expression [e] in the old
	   environment [env], and match the resulting value against the
	   pattern [p]. Accumulate the resulting bindings in the new
	   environment [new_env]. The type-checker guarantees that no
	   variable is bound twice. *)
	match_irrefutable_pattern new_env p (eval env e)
      ) env equations

  | DMultiple (Recursive, equations) ->
      (* We must construct an environment and a number of closures
	 that point to each other; this is Landin's knot. We begin
         by constructing a list of partly initialized closures, as
         well as the new environment, which contains these closures. *)
      let (new_env : env), (closures : closure list) =
	List.fold_left (fun (new_env, closures) (p, e) ->
	  match p, e with
	  | PVar f, EFun (_type_parameters, argument_type, _result_type, body) ->
	      (* Build a closure with an uninitialized environment field. *)
	      let c = {
		(* The argument pattern is implicit in the argument type. *)
		arg = type_to_pattern argument_type;
		(* The function body. *)
		body = body;
		(* An uninitialized environment. *)
		env = empty;
	      } in
	      (* Bind [f] to this closure. *)
	      extend_unqualified_variable f (VClosure c) new_env,
	      c :: closures
	  | _, _ ->
	      (* The left-hand side of a recursive definition must be a variable,
		 and the right-hand side must be a lambda-abstraction. *)
	      (* TEMPORARY should deal with PLocated too *)
	      assert false
	) (env, []) equations
      in
      (* There remains to patch the closures with the new environment. *)
      List.iter (fun c ->
	(* TEMPORARY environment could/should be filtered? *)
        c.env <- new_env
      ) closures;
      (* Done. *)
      new_env

(* ---------------------------------------------------------------------------- *)

(* Evaluating a concrete data type definition. *)

let evaluate_data_type_def (env : env) (branches : data_type_def_rhs) : env =
  snd (
    (* For each data constructor, *)
    List.fold_left (fun (index, env) (datacon, defs) ->
      (* Compute the number of fields, and create a mapping of field names
	 to field indices. *)
      let arity, fields =
	List.fold_left (fun (arity, fields) def ->
	  match def with
	  | FieldValue (f, _) ->
	      arity + 1, Variable.Map.add f arity fields
	  | FieldPermission _ ->
	      arity, fields
	) (0, Variable.Map.empty) defs
      in
      (* Generate a new data constructor information record. *)
      let info = {
	datacon_name = Datacon.print datacon;
	datacon_arity = arity;
	datacon_index = index;
	datacon_fields = fields;
      } in
      (* Extend the environment with it. *)
      index + 1,
      extend_unqualified_datacon datacon info env
    ) (0, env) branches
  )

(* ---------------------------------------------------------------------------- *)

(* Evaluating a toplevel implementation item. *)

let eval_implementation_item (env : env) (item : toplevel_item) : env =
  match item with
  | ValueDeclarations defs ->
      List.fold_left eval_value_definition env defs
  | OpenDirective m ->
      (* Assuming that the module [m] has been evaluated before, the (public)
	 qualified names that it has declared are available in the environment.
	 For each name of the form [m::x], we create a new local name [x]. *)
      unqualify m env
  | DataTypeGroup (_, defs) ->
      (* The effect of evaluating a data type definition is to generate new
	 data constructors. *)
      List.fold_left (fun env def ->
        match def with
        | Concrete (_, _, rhs, _) ->
            evaluate_data_type_def env rhs
        | Abstract _ ->
            env
      ) env defs
  | PermDeclaration _ ->
      (* We are evaluating an implementation, not an interface. *)
      assert false

(* ---------------------------------------------------------------------------- *)

(* Evaluating an implementation. *)

let eval_implementation (env : env) (impl : implementation) : env =
  List.fold_left eval_implementation_item env impl

(* ---------------------------------------------------------------------------- *)

(* Evaluating (exporting) an interface. *)

(* An interface is evaluated as if it were a record construction expression, in
   the environment obtained by evaluating the corresponding implementation. Thus,
   evaluating the interface has the effect of picking, in the environment produced
   by evaluating the implementation, the (variable and data constructor) bindings
   that are meant to be exported. *)

(* [m] is the name of the module that we are constructing. The environment [env]
   contains the unqualified bindings produced by evaluating the implementation of [m],
   and also serves as an accumulator, where we produce qualified bindings for [m]. *)

let export_interface_item (m : Module.name) (env : env) (item : toplevel_item) : env =
  match item with
  | ValueDeclarations _ ->
      (* We are evaluating an interface, not an implementation. *)
      assert false
  | OpenDirective _ ->
      (* An [open] directive does not affect the set of names that are exported.
         Thus, it is ignored. *)
      env
  | DataTypeGroup (_, defs) ->
      (* The effect of a data type declaration is to export data constructors. *)
      List.fold_left (fun env def ->
        match def with
        | Concrete (_, _, branches, _) ->
	    (* For each data constructor, *)
	    List.fold_left (fun env (datacon, _) ->
	      (* Export this data constructor. *)
		{ env with datacons = D.qualify m datacon env.datacons }
	    ) env branches
        | Abstract _ ->
            env
      ) env defs
  | PermDeclaration (x, _) ->
      (* The effect of a variable declaration is to export this variable. *)
      { env with variables = V.qualify m x env.variables }

let export_interface (m : Module.name) (env : env) (intf : interface) : env =
  (* Create qualified names for the things mentioned in the interface. *)
  let env = List.fold_left (export_interface_item m) env intf in
  (* Remove all unqualified bindings. *)
  zap env

(* ---------------------------------------------------------------------------- *)

(* Evaluating an interface/implementation pair. *)

(* When this function is invoked, the environment [env] contains no unqualified
   bindings. The new environment returned by this function satisfies the same
   property. *)

let eval_unit (env : env) (m : Module.name) (intf : interface) (impl : implementation) : env =
  (* Evaluate the implementation. *)
  let env = eval_implementation env impl in
  (* Export the interface. *)
  export_interface m env intf

(* ---------------------------------------------------------------------------- *)

(* Evaluating a lone implementation is permitted for convenience, but does not
   return an updated environment. *)

let eval_lone_implementation (env : env) (impl : implementation) : unit =
  (* Evaluate the implementation. *)
  let _ = eval_implementation env impl in
  (* Drop the resulting environment. *)
  ()

