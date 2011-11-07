(* This module defines the syntax of types and algebraic data type
   definitions. *)

(* Names for algebraic data types. *)
type tycon

(* Names for data constructors. *)
type datacon

(* Names for fields. *)
type field

(* Type variables are de Bruijn indices. *)
type typevar =
    int

(* Term variables are de Bruijn indices. *)
type termvar =
    int

(* Definitions for algebraic data types. *)

(* A data type definition consists primarily of a list of branches. *)

(* A data type definition is parameterized with a vector of type
   variables [alphas] and with a vector of term variables [xs].
   The lengths of these vectors appear in the definition. *)

(* The definition may be marked as [exclusive], which allows certain
   fields as well as the tag itself to be considered mutable, and
   allows adoption. For the moment, these aspects are not reflected. *)

type definition = {
  type_parameters: int;
  term_parameters: int;
  branches: branch list
}

(* A branch in a data type definition is labeled with a data constructor
   and carries a list of typed fields. *)

and branch = {
  datacon: datacon;
  fields: (field * typ) list
}

(* A type is one of:
   - a folded concrete type (an instance of an algebraic data type);
   - an unfolded concrete type (a branch of an algebraic data type);
   - an abstract type (this includes primitive types, user-defined
     abstract types, and type variables);
   - a singleton type (which expresses an equality with a term variable);
   - the top type [none], which represents no permission/information at all.
*)

and typ =
  | TyConcreteFolded of concrete_type
  | TyConcreteUnfolded of unfolded_concrete_type
  | TyAbstract of abstract_type
  | TySingleton of termvar
  | TyTop

and concrete_type =
    tycon instance

and unfolded_concrete_type =
    datacon * (field * typ) list

and abstract_type =
    typevar instance

(* An instance of something is an application of this thing to a number
   of actual type and term parameters. *)

and 'a instance =
    'a * typ list * termvar list

(* Functions. *)

(* Find the definition of an algebraic data type. *)

let find_tycon : tycon -> definition =
  assert false (* TEMPORARY *)

(* Find a specific branch in a definition. *)

let find_branch : definition -> datacon -> branch option =
  assert false (* TEMPORARY *)

(* Instantiate a type. *)

let rec de_bruijn_subst env x =
  match env, x with
  | data :: _, 0 ->
      data
  | _ :: env, _ ->
      de_bruijn_subst env (x - 1)
  | [], _ ->
      x

let rec instantiate_ty type_params term_params ty : typ =
  match ty with
  | TyConcreteFolded cty ->
      TyConcreteFolded (instantiate_instance type_params term_params cty)
  | TyConcreteUnfolded (datacon, fields) ->
      TyConcreteUnfolded (datacon, instantiate_fields type_params term_params fields)
  | TyAbstract aty ->
      TyAbstract (instantiate_instance type_params term_params aty)
  | TySingleton x ->
      TySingleton (de_bruijn_subst term_params x)
  | TyTop ->
      TyTop

and instantiate_instance : 'a. typ list -> termvar list -> 'a instance -> 'a instance =
  (* polymorphic recursion required here! *)
  fun type_params term_params (con, types, terms) ->
  (
    con,
    List.map (instantiate_ty type_params term_params) types,
    List.map (de_bruijn_subst term_params) terms
  )

and instantiate_fields type_params term_params fields =
  List.map (fun (field, ty) ->
    field, instantiate_ty type_params term_params ty
  ) fields

(* Expand the definition of a concrete type. This function produces a
   pair of the (uninstantiated) algebraic data type definition and an
   instantiation function that must be applied to the types found in
   the definition. (This allows lazy instantiation.) *)

let unfold_concrete_type (cty : concrete_type) : (typ -> typ) * definition =
  let (tycon, type_params, term_params) = cty in
  let definition = find_tycon tycon in
  assert (definition.type_parameters = List.length type_params);
  assert (definition.term_parameters = List.length term_params);
  let instantiate = instantiate_ty type_params term_params in
  instantiate, definition

