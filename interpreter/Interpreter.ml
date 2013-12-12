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

(* The interpreter is written with simplicity, as opposed to efficiency, in
   mind. *)

(* TEMPORARY replace all occurrences of "assert false" with an appropriate
   error message: 1- suggest that the code is ill-typed; 2- print a location;
   3- only then, raise an exception. *)

(* ---------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------- *)

(* The interpreter treats data constructor definitions as generative. That is,
   the evaluation of a data constructor definition causes the generation of a
   fresh information record, to which the data constructor becomes bound. The
   type [datacon_info] is defined in [SurfaceSyntax]. Data constructors are
   treated just like variables: i.e., they are bound in the environment. This
   implies, for instance, that if a function refers to a data constructor,
   then this data constructor is interpreted in the closure's environment. We
   adopt this approach because it seems simple, efficient, and deals correctly
   with masking. *)

(* ---------------------------------------------------------------------------- *)

(* Thus, we have two namespaces: variables and data constructors. *)

module V =
  Namespace.MakeNamespace(Variable)

module D =
  Namespace.MakeNamespace(Datacon)

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

(* A special [datacon_info] record is created to represent arrays. The
   information held in this record is irrelevant; only its address is
   used to recognize an array. *)

let array_datacon_info : datacon_info = {
  datacon_name = "";
  datacon_arity = -1;
  datacon_index = 0;
  datacon_fields = Field.Map.empty;
  datacon_flavor = DataTypeFlavor.Mutable;
}

let is_array info =
  array_datacon_info == info

(* In the interpreter, an array is represented as a block of memory.
   This implies that it has an adopter field. *)

let makeArray (r : value array) : value =
  VAddress {
    tag = array_datacon_info;
    adopter = None;
    fields = r
  }

(* ---------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------- *)

(* A pretty-printer for values. *)

module ValuePrinter = struct

  open MzPprint

  (* The [depth] parameter is incremented at every memory block, and
     we stop when it reaches a hard-coded limit. This prevents entering
     an infinite loop when the heap is cyclic. It also helps visualize
     huge values. *)

  let rec print_value (depth : int) (v : value) : document =
    if depth >= 5 then
      string "..."
    else
      match v with
      | VInt i ->
         OCaml.int i
      | VAddress b ->
         let info = b.tag in
         if is_array info then
           (* An array. *)
           let vs = Array.to_list b.fields in
           array_with_nesting (
             separate_map semibreak (print_value depth) vs
           )
         else begin
           (* A memory block. *)
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
              utf8string info.datacon_name
           | _ :: _ ->
              utf8string info.datacon_name ^^ space ^^ braces_with_nesting (
                separate_map semibreak (fun (_, field, v) ->
                  (utf8string field ^^ space ^^ equals) ^//^
                    print_value (depth + 1) v
                ) fields
              )
           end
         end
      | VTuple vs ->
         parens_with_nesting (
           separate_map commabreak (print_value depth) vs
         )
      | VClosure _
      | VBuiltin _ ->
         string "<fun>"

  let print_value v =
    print_value 0 v

  let render v : string =
    render (print_value v)

end

(* ---------------------------------------------------------------------------- *)

(* An empty interpreter environment. *)

let empty : env = {
  variables = V.empty;
  datacons = D.empty;
}

(* Resolving a reference to a data constructor. Remember that the type-checker
   has not been run, so we cannot use the [datacon_info] field of the data
   constructor reference object; instead, we use the [datacon_unresolved]
   field, and look up the environment that the interpreter has constructed. *)

let resolve_datacon_reference (dref : datacon_reference) (env : env) : datacon_info =
  try
    D.lookup_maybe_qualified dref.datacon_unresolved env.datacons
  with Not_found ->
    (* Unknown data constructor. *)
    assert false

(* Extending the environment with a new unqualified variable. *)

let extend_unqualified_variable x v env =
  { env with variables = V.extend_unqualified x v env.variables }

(* Extending the environment with a new unqualified data constructor. *)

let extend_unqualified_datacon x info env =
  { env with datacons = D.extend_unqualified x info env.datacons }

(* Freezing a module. *)

let freeze m env =
  {
    variables = V.freeze m env.variables;
    datacons = D.freeze m env.datacons;
  }

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

(* Displaying an environment. *)

module EnvPrinter = struct

  open PPrint

  let print_datacon_info (_ : datacon_info) : document =
    string "<info>" (* TEMPORARY to be completed *)

  let print_env env : document =
    concat [
      string "Variables:"         ^//^ V.print_global_env ValuePrinter.print_value env.variables;
      string "Data constructors:" ^//^ D.print_global_env print_datacon_info env.datacons;
    ]

  let p (buf : Buffer.t) (env : env) =
    ToBuffer.pretty 0.95 Bash.twidth buf (print_env env)

  (* Avoid a warning if this printer is unused. *)
  let _ =
    p

end

(* ---------------------------------------------------------------------------- *)

(* Constant value definitions. *)

(* The unit value is the empty tuple. *)

let unit_value =
  VTuple []

(* The Boolean values are [bool::True] and [bool::False]. Unfortunately, these
   are not constants, because we need to find the [datacon_info] records
   associated with these data constructors. (If required, we could fake them,
   but let's not bother. This is not performance-critical anyway: these Boolean
   values are produced only by the evaluation of [EOwn] and [==].) TEMPORARY *)

let bool =
  Module.register "bool"

let boolean_value datacon env =
  (* We assume that the module [bool] has been loaded at this point.
     This implies that the primitive operations which manufacture a
     Boolean result cannot be defined in the module [bool], but only
     in a later module. *)
  let info =
    try
      D.lookup_qualified bool datacon env.datacons
    with Not_found ->
      (* Unknown data constructor. *)
      Log.error "Interpreter: failed to find the built-in data constructor: bool::%s" (Datacon.print datacon)
  in
  VAddress { tag = info; adopter = None; fields = [||] }

let false_value =
  boolean_value (Datacon.register "False")

let true_value =
  boolean_value (Datacon.register "True")

let bool (env : env) (b : bool) =
  if b then true_value env else false_value env

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

let asPair view1 view2 (v : value) =
  match asTuple v with
  | [ v1; v2 ] ->
      view1 v1, view2 v2
  | _ ->
      (* Runtime arity error. *)
      assert false

let asTriple view1 view2 view3 (v : value) =
  match asTuple v with
  | [ v1; v2; v3 ] ->
      view1 v1, view2 v2, view3 v3
  | _ ->
      (* Runtime arity error. *)
      assert false

let asQuintuple view1 view2 view3 view4 view5 (v : value) =
  match asTuple v with
  | [ v1; v2; v3; v4; v5 ] ->
      view1 v1, view2 v2, view3 v3, view4 v4, view5 v5
  | _ ->
      (* Runtime arity error. *)
      assert false

let asArray (v : value) : value array =
  let b = asBlock v in
  b.fields

let asValue (v : value) : value =
  v

let asIntPair =
  asPair asInt asInt

(* ---------------------------------------------------------------------------- *)

(* Evaluating an application of a built-in function. *)

let eval_builtin (env : env) (loc : location) (b : string) (v : value) : value =
  (* The primitive operations that operate on integers are already
     implemented in [MezzoLib], and can be re-used. *)
  let open MezzoLib in
  match b with
  | "_mz_iadd" ->
      VInt (_mz_iadd (asIntPair v))
  | "_mz_isub" ->
      VInt (_mz_isub (asIntPair v))
  | "_mz_imul" ->
      VInt (_mz_imul (asIntPair v))
  | "_mz_idiv" ->
      VInt (_mz_idiv (asIntPair v))
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
      VInt (_mz_iand (asIntPair v))
  | "_mz_address_eq" ->
      let b1, b2 = asPair asBlock asBlock v in
      bool env (b1 == b2)
  | "_mz_print_value" ->
      print_endline (ValuePrinter.render v);
      unit_value
  | "_mz_magic" ->
      v
  | "_mz_array_create" ->
      let n, v = asPair asInt asValue v in
      begin try
       makeArray (Array.create n v)
      with Invalid_argument _ ->
       Log.error "%aInvalid length at array creation: %d.\n" Lexer.p loc n
      end
  | "_mz_array_unsafe_get"
  | "_mz_array_get" ->
      let r, i = asPair asArray asInt v in
      begin try
       r.(i)
      with Invalid_argument _ ->
       Log.error "%aInvalid index at array access: %d (%d).\n" Lexer.p loc i (Array.length r)
      end
  | "_mz_array_unsafe_set"
  | "_mz_array_set" ->
      let r, i, v = asTriple asArray asInt asValue v in
      begin try
       r.(i) <- v;
       unit_value
      with Invalid_argument _ ->
       Log.error "%aInvalid index at array update: %d (%d).\n" Lexer.p loc i (Array.length r)
      end
  | "_mz_array_length" ->
      let r = asArray v in
      VInt (Array.length r)
  | "_mz_array_unsafe_sub" ->
      let r, ofs, len = asTriple asArray asInt asInt v in
      makeArray (Array.sub r ofs len)
  | "_mz_array_append_prim" ->
      let r1, r2 = asPair asArray asArray v in
      makeArray (Array.append r1 r2)
  | "_mz_array_unsafe_blit" ->
      let r1, ofs1, r2, ofs2, len = asQuintuple asArray asInt asArray asInt asInt v in
      Array.blit r1 ofs1 r2 ofs2 len;
      unit_value
  | _ ->
      Log.error "%aUnknown builtin function: %s\n" Lexer.p loc b

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
  | PConstruct (dref, fps) ->
      let b = asBlock v in
      let info = resolve_datacon_reference dref env in
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
  | PAs (p1, x2) ->
      let env = match_pattern env p1 v in
      let env = match_pattern env (PVar x2) v in
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

let rec eval (env : env) (loc : location) (e : expression) : value =
  match e with

  | EConstraint (e, _) ->
      eval env loc e

  | EVar x ->
      begin try
       V.lookup_maybe_qualified x env.variables
      with Not_found ->
       (* Unknown variable. *)
       assert false
      end

  (* Most builtin expressions produce a builtin value (a function), but some
     builtin expressions produce a value of some other nature. *)

  | EBuiltin "_mz_array_max_length" ->
      VInt Sys.max_array_length (* TEMPORARY possibly minus one *)

  | EBuiltin b ->
      VBuiltin b

  | ELet (rec_flag, equations, body) ->
      let env = eval_definitions env (loc, rec_flag, equations) in
      eval env loc body

  | ELocalType (_, e)
  | ELetFlex (_, e) ->
      eval env loc e

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

  | EAssign (e1, f, e2) ->
      (* We rely on the fact that [b1.tag] is a [datacon_info] record and
         contains a mapping of field names to field offsets. *)
      let b1 = asBlock (eval env loc e1) in
      let v2 = eval env loc e2 in
      b1.fields.(field_offset f.field_name b1.tag) <- v2;
      unit_value

  | EAssignTag (e, dref, _) ->
      (* We do not assume that the type-checker has annotated the abstract
        syntax tree, so we cannot use the [tag_update_info] component. *)
      let b = asBlock (eval env loc e) in
      b.tag <- resolve_datacon_reference dref env;
      unit_value

  | EAccess (e, f) ->
      (* We rely on the fact that [b.tag] is a [datacon_info] record and
         contains a mapping of field names to field offsets. *)
      let b = asBlock (eval env loc e) in
      b.fields.(field_offset f.field_name b.tag)

  | EPack _
  | EAssert _ ->
      unit_value

  | EApply (e1, e2) ->
      let v1 = eval env loc e1 in
      let v2 = eval env loc e2 in
      begin match v1 with
      | VClosure c1 ->
         (* Extend the closure's environment with a binding of the
            formal argument to the actual argument. Evaluate the
            closure body. *)
         eval (match_irrefutable_pattern c1.env c1.arg v2) loc c1.body
      | VBuiltin b ->
         eval_builtin env loc b v2
      | _ ->
         (* Runtime tag error. *)
         assert false
      end

  | ETApply (e, _) ->
      eval env loc e

  | EMatch (_, e, branches) ->
      switch env loc (eval env loc e) branches

  | ETuple es ->
      (* [List.map] implements left-to-right evaluation. *)
      VTuple (List.map (eval env loc) es)

  | EConstruct (dref, fes) ->
      (* Evaluate the fields in the order specified by the programmer. *)
      let fvs =
       List.map (fun (f, e) -> (f, eval env loc e)) fes
      in
      (* Allocate a field array. *)
      let info = resolve_datacon_reference dref env in
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
      let b = asBlock (eval env loc e) in
      eval env loc (if b.tag.datacon_index > 0 then e1 else e2)

  | EWhile (_, e1, e2) ->
      while (asBlock (eval env loc e1)).tag.datacon_index > 0  do
        ignore (eval env loc e2)
      done;
      unit_value
  
  | EFor (_, (x, _, _), e1, f, e2, e) ->
      let i1, i2 = asInt (eval env loc e1), asInt (eval env loc e2) in
      let body i =
        let env = match_irrefutable_pattern env (PVar x) (VInt i) in
        ignore (eval env loc e)
      in begin
      match f with
      | To -> for i = i1 to i2 do body i done
      | Downto -> for i = i1 downto i2 do body i done
      | Below -> for i = i1 to i2 - 1 do body i done
      | Above -> for i = i1 downto i2 + 1 do body i done
      end; unit_value

  | ESequence (e1, e2) ->
      let _unit = eval env loc e1 in
      eval env loc e2

  | ELocated (e, loc) ->
      (* This is where we update the parameter [loc]. *)
      eval env loc e

  | EInt i ->
      VInt i

  | EExplained e ->
      eval env loc e

  | EGive (e1, e2) ->
      let b1 = asBlock (eval env loc e1) in
      let b2 = asBlock (eval env loc e2) in
      assert (b1.adopter = None);
      b1.adopter <- Some b2;
      unit_value

  | ETake (e1, e2) ->
      let b1 = asBlock (eval env loc e1) in
      let b2 = asBlock (eval env loc e2) in
      begin match b1.adopter with
      | Some b when (b == b2) ->
          b1.adopter <- None;
          unit_value
      | _ ->
          Log.error "%aA take instruction failed.\n" Lexer.p loc
      end

  | EOwns (e2, e1) ->
      let b2 = asBlock (eval env loc e2) in
      let b1 = asBlock (eval env loc e1) in
      begin match b1.adopter with
      | Some b when (b == b2) ->
         true_value env
      | _ ->
          false_value env
      end

  | EFail ->
      Log.error "%aA fail instruction was encountered.\n" Lexer.p loc

(* ---------------------------------------------------------------------------- *)

(* Evaluating a switch construct. *)

and switch (env : env) (loc : location) (v : value) (branches : (pattern * expression) list) : value =
  match branches with
  | (p, e) :: branches ->
      begin match match_refutable_pattern env p v with
      | Some env ->
         (* [p] matches [v]. Evaluate the branch [e]. *)
         eval env loc e
      | None ->
         (* [p] does not match [v]. Try the next branch. *)
         switch env loc v branches
      end
  | [] ->
      (* No more branches. This should not happen if the type-checker has
         checked for exhaustiveness. At the moment, this is not done,
         though. *)
      Log.error "%aMatch failure. No pattern matches this value:\n%s" Lexer.p loc (ValuePrinter.render v)

(* ---------------------------------------------------------------------------- *)

(* Evaluating a value definition. *)

and eval_definitions (env : env) ((loc, rec_flag, equations) : definitions) : env =
  match rec_flag with
  | Nonrecursive ->
      (* Evaluate the equations, in left-to-right order. *)
      List.fold_left (fun new_env (p, e) ->
       (* For each equation [p = e], evaluate the expression [e] in the old
          environment [env], and match the resulting value against the
          pattern [p]. Accumulate the resulting bindings in the new
          environment [new_env]. The type-checker guarantees that no
          variable is bound twice. *)
       match_irrefutable_pattern new_env p (eval env loc e)
      ) env equations

  | Recursive ->
      (* We must construct an environment and a number of closures
        that point to each other; this is Landin's knot. We begin
         by constructing a list of partly initialized closures, as
         well as the new environment, which contains these closures. *)
      let (new_env : env), (closures : closure list) =
       List.fold_left eval_recursive_equation (env, []) equations
      in
      (* There remains to patch the closures with the new environment. *)
      List.iter (fun c ->
       (* TEMPORARY environment could/should be filtered? *)
        c.env <- new_env
      ) closures;
      (* Done. *)
      new_env

and eval_recursive_equation ((new_env, closures) as accu) (p, e) =
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
  | PLocated (p, _), _ ->
      eval_recursive_equation accu (p, e)
  | _, ELocated (e, _) ->
      eval_recursive_equation accu (p, e)
  | _, _ ->
      (* The left-hand side of a recursive definition must be a variable,
        and the right-hand side must be a lambda-abstraction. *)
      assert false

(* ---------------------------------------------------------------------------- *)

(* Evaluating a concrete data type definition. *)

let evaluate_data_type_def
    (env : env) (global_flavor: DataTypeFlavor.flavor) (branches : data_type_def_branch list) : env =
  snd (
    (* For each data constructor, *)
    List.fold_left (fun (index, env) (branch_flavor, datacon, _bindings, defs) ->
      (* Compute the number of fields, and create a mapping of field names
        to field indices. *)
      let arity, fields =
      List.fold_left (fun (arity, fields) def ->
        match def with
        | FieldValue (f, _) ->
            arity + 1, Variable.Map.add f arity fields
        | FieldPermission _ ->
            arity, fields
      ) (0, Variable.Map.empty) defs in
      (* Generate a new data constructor information record. *)
      let info = {
        datacon_name = Datacon.print datacon;
        datacon_arity = arity;
        datacon_index = index;
        datacon_fields = fields;
        datacon_flavor =
	  DataTypeFlavor.join global_flavor branch_flavor
	    (fun () -> assert false) (* cannot happen *);
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
  | ValueDefinitions defs ->
      eval_definitions env defs
  | OpenDirective m ->
      (* Assuming that the module [m] has been evaluated before, the (public)
        qualified names that it has declared are available in the environment.
        For each name of the form [m::x], we create a new local name [x]. *)
      unqualify m env
  | DataTypeGroup (_, _, defs) ->
      (* The effect of evaluating a data type definition is to generate new
        data constructors. *)
      List.fold_left (fun env def ->
        match def.rhs with
        | Concrete (f, rhs, _) ->
            evaluate_data_type_def env f rhs
        | Abstract _
        | Abbrev _ ->
            env
      ) env defs
  | ValueDeclaration _ ->
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
  | ValueDefinitions _ ->
      (* We are evaluating an interface, not an implementation. *)
      assert false
  | OpenDirective _ ->
      (* An [open] directive does not affect the set of names that are exported.
         Thus, it is ignored. *)
      env
  | DataTypeGroup (_, _, defs) ->
      (* The effect of a data type declaration is to export data constructors. *)
      List.fold_left (fun env def ->
        match def.rhs with
        | Concrete (_, branches, _) ->
           (* For each data constructor, *)
           List.fold_left (fun env (_, datacon, _, _) ->
             (* Export this data constructor. *)
              { env with datacons = D.qualify m datacon env.datacons }
           ) env branches
        | Abstract _
        | Abbrev _ ->
            env
      ) env defs
  | ValueDeclaration ((x, _, _), _) ->
      (* The effect of a variable declaration is to export this variable. *)
      { env with variables = V.qualify m x env.variables }

let export_interface (m : Module.name) (env : env) (intf : interface) : env =
  (* Create qualified names for the things mentioned in the interface. *)
  let env = List.fold_left (export_interface_item m) env intf in
  (* Freeze this module, i.e. mark that it exists, and promise that we will not
     modify it any more. (Not really necessary; may be useful for debugging.) *)
  let env = freeze m env in
  (* Remove all unqualified bindings. *)
  zap env

(* ---------------------------------------------------------------------------- *)

(* Evaluating an interface/implementation pair. *)

(* When this function is invoked, the environment [env] contains no unqualified
   bindings. The new environment returned by this function satisfies the same
   property. *)

let eval_unit (env : env) (m : Module.name) (intf : interface) (impl : implementation) : env =
  Log.debug "Interpreter: evaluating module: %s." (Module.print m);
  (* Evaluate the implementation. *)
  let env = eval_implementation env impl in
  (* Export the interface. *)
  export_interface m env intf

(* ---------------------------------------------------------------------------- *)

(* Evaluating a lone implementation is permitted for convenience, but does not
   return an updated environment. *)

let eval_lone_implementation (env : env) (impl : implementation) : unit =
  Log.debug "Interpreter: evaluating a lone module.";
  (* Evaluate the implementation. *)
  let _ = eval_implementation env impl in
  (* Drop the resulting environment. *)
  ()

