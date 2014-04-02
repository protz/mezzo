open Kind
open SurfaceSyntax
open MzPprint

(* This is a printer for types in the surface syntax. The structure of the
   printer mirrors the structure of the grammar. *)

(* ---------------------------------------------------------------------------- *)

(* The main group of mutually recursive functions. *)

let rec parenthetic_type ty =
  match ty with
  | TyLocated (ty, _) ->
      parenthetic_type ty
  | TyTuple [] ->
      string "()"
  | _ ->
      parens_with_nesting (arbitrary_type ty)

and atomic_type ty =
  match ty with
  | TyUnknown ->
      string "unknown"
  | TyDynamic ->
      string "dynamic"
  | TyEmpty ->
      string "empty"
  | TyVar x ->
      variable x
  | TyConcrete (_, _, None) ->
      concrete ty
  | _ ->
      parenthetic_type ty

and tight_type ty =
  match ty with
  | TySingleton (TyVar x) ->
      equals ^^ variable x
  | TySingleton _ ->
      assert false (* unexpected *)
  | TyApp (head, args) ->
      application tight_type head atomic_type args
  | _ ->
      atomic_type ty

and normal_type ty =
  match ty with
  | TyArrow (ty1, ty2) ->
        prefix 0 1
          (tight_type ty1 ^^ string " ->")
          (normal_type ty2)
  | TyForall (b, ty) ->
      (* TEMPORARY might wish to fuse adjacent quantifiers *)
      let bs = [ b ] in
      prefix 0 1
       (brackets (commas binding bs))
       (normal_type ty)
  | TyExists (b, ty) ->
      (* TEMPORARY might wish to fuse adjacent quantifiers *)
      let bs = [ b ] in
      prefix 0 1
       (braces (commas binding bs))
       (normal_type ty)
  | TyConcrete _ ->
      concrete ty
  | _ ->
      tight_type ty

and loose_type ty =
  match ty with
  | TyAnchoredPermission (TyVar x, TySingleton (TyVar y)) ->
      (* A special case: syntactic sugar for equations. *)
      variable x ^^ string " = " ^^ variable y
  | TyAnchoredPermission (TyVar x, ty) ->
      prefix 2 1
        (variable x ^^ string " @")
        (normal_type ty)
  | TyAnchoredPermission _ ->
      assert false (* unexpected *)
  | TyNameIntro (x, ty) ->
      prefix 2 1
        (unqualified_variable x ^^ colon)
        (normal_type ty)
  | _ ->
      normal_type ty

and consumes_type ty =
  match ty with
  | TyConsumes ty ->
      prefix 2 1
       (string "consumes")
       (loose_type ty)
  | _ ->
      loose_type ty

and very_loose_type ty =
  match ty with
  | TyStar (ty1, ty2) ->
      prefix 0 1
       (consumes_type ty1 ^^ string " *")
        (very_loose_type ty2)
  | TyTuple ((_ :: _ :: _) as tys) ->
      (* I do not insert parentheses by default. They will be inserted
        if required. *)
      group (separate_map commabreak consumes_type tys)
  | TyTuple [ _ ] ->
      assert false (* unexpected *)
  | _ ->
      consumes_type ty

and fat_type ty =
  match ty with
  | TyBar (TyTuple [], ty2) ->
      (* A special case for (| p). *)
      string "| " ^^ very_loose_type ty2
  | TyBar (ty1, ty2) ->
      (* either:
        t | p
        or:
          t
        | p
      *)
      group (
       nest 2 (break 0 ^^ fat_type ty1) ^/^
       string "| " ^^ nest 2 (very_loose_type ty2)
      )
  | TyAnd (c, ty) ->
      (* Same appearance as above. *)
      group (
        nest 2 (break 0 ^^ fat_type ty) ^/^
        string "| " ^^ nest 2 (mode_constraint c)
      )
  | _ ->
      very_loose_type ty

and arbitrary_type ty =
  fat_type ty

(* ---------------------------------------------------------------------------- *)

(* Auxiliary functions for certain special cases and sub-categories. *)

and unqualified_variable x =
  string (Variable.print x)

and variable x =
  string (print_maybe_qualified Variable.print x)

and binding (x, kind, _) =
  match kind with
  | KType ->
      unqualified_variable x
  | KTerm
  | KPerm ->
      unqualified_variable x ^^ ccolon ^^ print_kind kind
  | KArrow _ ->
      assert false (* unexpected *)

and concrete ty =
  match ty with
  | TyConcrete (dref, fs, clause) ->
      datacon_reference dref ^^
      (
       if List.length fs > 0 then
         space ^^ braces_with_nesting (separate_map semibreak field fs)
       else
         empty
      ) ^^
      (
       match clause with
       | None ->
           empty
       | Some clause ->
           string " adopts " ^^ normal_type clause
      )
  | _ ->
    assert false (* cannot happen *)

and field = function
  | f, TySingleton (TyVar y) ->
      (* A special case: syntactic sugar for equations. *)
      utf8string (Field.print f) ^^ string " = " ^^ variable y
  | f, ty ->
      prefix 2 1
       (utf8string (Field.print f) ^^ colon)
       (normal_type ty)

and mode_constraint (mode, ty) =
  string (Mode.print mode) ^^ space ^^ atomic_type ty

and datacon_reference dref =
  utf8string (print_maybe_qualified Datacon.print dref.datacon_unresolved)

(* ---------------------------------------------------------------------------- *)

(* The main entry point. *)

let print =
  arbitrary_type

let p buf t =
  pdoc buf (arbitrary_type, t)
