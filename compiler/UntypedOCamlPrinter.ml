(* This is a pretty-printer for Untyped OCaml. *)

open Hml_Pprint
open UntypedOCaml

(* ---------------------------------------------------------------------------- *)

(* Tuples and records. *)

let tuple print components =
  parens_with_nesting (
    separate_map commabreak print components
  )

let record print fields =
  braces_with_nesting (
    separate_map semibreak (fun (field, thing) ->
      (utf8string field ^^ space ^^ equals) ^//^ print thing
    ) fields
  )

(* ---------------------------------------------------------------------------- *)

(* Patterns. *)

(* An atomic pattern is well-delimited. *)

let rec atomic_pattern (p : pattern) : document =
  match p with
  | PVar x ->
      utf8string x
  | PAny ->
      underscore
  | PTuple [ p ] ->
      atomic_pattern p
  | PTuple ps ->
      tuple normal_pattern ps
  | PRecord fps ->
      record normal_pattern fps
  | PConstruct _
  | PAs _ ->
      parens_with_nesting (pattern p)

(* A normal pattern can be a tuple or record component, i.e., it binds
   tighter than a comma or semicolon. *)

and normal_pattern p =
  match p with
  | PConstruct (datacon, ps) ->
      utf8string datacon ^^ space ^^ atomic_pattern (PTuple ps)
  | _ ->
      atomic_pattern p

(* A dangerous pattern cannot be a tuple or record component. *)

and dangerous_pattern = function
  | PAs (p, x) ->
      group (dangerous_pattern p ^/^ string "as " ^^ utf8string x)
  | p ->
      normal_pattern p

and pattern p =
  dangerous_pattern p

(* ---------------------------------------------------------------------------- *)

(* Expressions. *)

(* An atomic expression is in principle well-delimited. As a slight extension
   of this class, we allow field access expressions (when the object is itself
   an atomic expression). *)

let rec atomic_expression (e : expression) : document =
  match e with
  | EVar x ->
      utf8string x
  | EInfixVar x ->
      parens (utf8string x)
  | ETuple [ e ] ->
      atomic_expression e
  | ETuple es ->
      tuple normal_expression es
  | ERecord fes ->
      record normal_expression fes
  | EInt i ->
      if i >= 0 then OCaml.int i else parens (OCaml.int i)
  | EStringLiteral s ->
      OCaml.string s
  | EAccess (e, field) ->
      atomic_expression e ^^ dot ^^ utf8string field
  | EMatch (e, branches) ->
      group (
	surround 2 1
	  (string "begin match")
	  (expression e)
	  (string "with")
	^^
	concat_map (fun (p, e) ->
	  break 1 ^^ string "| " ^^ branch 4 p e
	) branches ^^
	break 1 ^^ string "end"
      )
  | _ ->
      group (parens (expression e))

(* Prefix applications. *)

(* In order to indent all arguments at the same level, we accummulate
   them in [arguments] until we reach the application head. *)

and prefix_application arguments = function
  | EApply (e1, e2) ->
      prefix_application (e2 :: arguments) e1
  | EConstruct (datacon, es) ->
      prefix_application (ETuple es :: arguments) (EVar datacon)
  | ESetField (e1, f, e2) ->
      prefix_application (e1 :: (EInt f) :: e2 :: arguments) (EVar "Obj.set_field")
  | ESetTag (e, i) ->
      prefix_application (e :: (EInt i) :: arguments) (EVar "Obj.set_tag")
  | EGetField (e, f) ->
      prefix_application (e :: (EInt f) :: arguments) (EVar "Obj.field")
  | EGetTag e ->
      prefix_application (e :: arguments) (EVar "Obj.tag")
  | EMagic e ->
      prefix_application (e :: arguments) (EVar "Obj.magic")
  | ERepr e ->
      prefix_application (e :: arguments) (EVar "Obj.repr")
  | head ->
      group (
	atomic_expression head ^^ nest 2 (
	  concat_map (fun arg -> break 1 ^^ atomic_expression arg) arguments
	)
      )

(* Infix applications. *)

and infix_application = function
  | EApply (EApply (EInfixVar op, e1), e2) ->
      group (
        prefix_application [] e1 ^/^ string op ^/^ prefix_application [] e2
      )
  | e ->
      prefix_application [] e

(* A normal expression can be a tuple or record component, i.e., it binds
   tighter than a comma or semicolon. At this level, we find function
   applications. *)

and normal_expression e =
  infix_application e

(* A sequence expression can appear as a component in a sequence, and can
   itself be a sequence, since the semicolon is associative. *)

and sequence_expression = function
  | EAssign (e1, f, e2) ->
      group (
	(atomic_expression e1 ^^ dot ^^ utf8string f ^^ larrow) ^//^
	  normal_expression e2
      )
  | ESequence (e1, e2) ->
      sequence_expression e1 ^^ semi ^^ hardline ^^
      sequence_expression e2
  | e ->
      normal_expression e

(* A dangling expression is an expression whose right end is not clearly
   delimited. Neverthless, it binds tighter than BAR, i.e. a BAR will end
   it, so the branches of a [match] construct can be dangling expressions. *)

and dangling_expression = function
  | ELet (f, eqs, body) ->
      group (
	string "let " ^^
	flag f ^^
	equations eqs ^/^
	string "in"
      )
      ^^ hardline ^^
      dangling_expression body
  | EFun (p, body) ->
      string "function " ^^ branch 2 p body
  | EIfThenElse (c, e1, e2) ->
      group (
	surround 2 1
	  (string "if")
	  (normal_expression c)
	  (string "then")
	^^
	nest 2 (break 1 ^^ normal_expression e1)
	^/^ string "else" ^^
	nest 2 (break 1 ^^ normal_expression e2)
      )
  | e ->
      sequence_expression e

and flag = function
  | SurfaceSyntax.Nonrecursive ->
      empty
  | SurfaceSyntax.Recursive ->
      string "rec "

and branch (n : int) p e =
  group (
    pattern p ^^ string " ->" ^^ nest n (break 1 ^^ 
      dangling_expression e
    )
  )

and equations eqs =
  separate_map
    (string "and" ^^ break 1)
    equation
    eqs

and equation (p, e) =
  (pattern p ^^ space ^^ equals) ^//^ expression e

(* An arbitrary expression. *)

and expression e =
  dangling_expression e

(* ---------------------------------------------------------------------------- *)

(* Types. *)

let ty = function
  | TyVar x ->
      utf8string x

let data_type_def_branch (datacon, components) =
  hardline ^^
  string "| " ^^
  utf8string datacon ^^
  match components with
  | [] ->
      empty
  | _ :: _ ->
      string " of " ^^ separate_map (string " * ") ty components

let data_type_def_lhs (typecon, parameters) =
  begin match parameters with
  | [] ->
      empty
  | [ x ] ->
      utf8string x ^^ space
  | _ :: _ :: _ ->
      tuple utf8string parameters ^^ space
  end ^^
  utf8string typecon

let mutability = function
  | Immutable ->
      empty
  | Mutable ->
      string "mutable "

let record_def (fields : record_def) =
  braces_with_nesting (
    separate_map semibreak (fun (m, f, t) ->
      (mutability m ^^ utf8string f ^^ colon) ^//^ ty t
    ) fields
  )

let data_type_def_rhs = function
  | Sum branches ->
      concat_map data_type_def_branch branches
  | Record def ->
      break 1 ^^ record_def def

let data_type_def (lhs, rhs) =
  group (
    string "type " ^^ data_type_def_lhs lhs ^^ space ^^ equals ^^ nest 2 (data_type_def_rhs rhs)
  )

(* ---------------------------------------------------------------------------- *)

(* Value definitions. *)

let definition (f, eqs) =
  group (
    string "let " ^^
    flag f ^^
    equations eqs
  )

(* ---------------------------------------------------------------------------- *)

(* Top-level items. *)

let toplevel_item = function
  | DataTypeGroup def ->
      data_type_def def
  | ValueDefinition def ->
      definition def
  | ValueDeclaration (x, t) ->
      string "val " ^^ utf8string x ^^ colon ^^ space ^^ ty t
  | OpenDirective m ->
      string "open " ^^ string m

let implementation items =
  concat_map (fun item ->
    toplevel_item item ^^ twice hardline
  ) items

let interface =
  implementation

