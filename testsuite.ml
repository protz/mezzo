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

module K = KindCheck

open Kind
open TypeCore
open Types
open TestUtils
open TypeErrors

let drop_derivation =
  Derivations.drop_derivation
;;

let check env point t =
  match Permissions.sub env point t with
  | Some _, _ ->
      ()
  | None, d ->
      raise_error env (ExpectedType (t, point, d))
;;

let point_by_name env ?mname name =
  point_by_name env ?mname (Variable.register name)
;;

exception KnownFailure

let silent_warn_error =
  "@1..5"
;;

let pedantic_warn_error =
  "+1..4@5"
;;

let simple_test ?(warn_error=silent_warn_error) ?known_failure outcome = fun do_it ->
  let known_failure = Option.unit_bool known_failure in
  let raise_if (e: exn): unit =
    if not known_failure then
      raise e
    else
      raise KnownFailure
  in
  let success_if (): unit =
    if known_failure then
      raise (Failure "Test started working, remove ~known_failure!")
  in
  try
    TypeErrors.parse_warn_error warn_error;
    ignore (do_it ());
    match outcome with
    | KFail ->
        raise_if (Failure "Test passed, it was supposed to fail")
    | Fail _ ->
        raise_if (Failure "Test passed, it was supposed to fail")
    | Pass ->
        success_if ()
  with
  | TypeCheckerError e ->
      let e = internal_extracterror e in
      begin match outcome with
      | Pass ->
          raise_if (Failure "Test failed, it was supposed to pass")
      | Fail f ->
          if f e then
            success_if ()
          else
            raise_if (Failure "Test failed but not for the right reason")
      | KFail ->
          raise_if (Failure "Test failed but not for the right reason")
      end

  | K.KindError _ ->
      begin match outcome with
      | Pass ->
          raise_if (Failure "Test failed, it was supposed to pass")
      | KFail ->
          success_if ()
      | Fail _ ->
          raise_if (Failure "Test failed but not for the right reason")
      end

  | Log.MzInternalFailure msg ->
      raise_if (Failure msg)
;;

let pass =
  simple_test Pass
;;

let pass_known_failure =
  simple_test ~known_failure:() Pass
;;

let fail =
  simple_test (Fail (function _ -> true))
;;

let kfail =
  simple_test KFail
;;

let fail_known_failure =
  simple_test ~known_failure:() (Fail (function _ -> true))
;;

let kfail_known_failure =
  simple_test ~known_failure:() KFail
;;

let dummy_loc =
  Lexing.dummy_pos, Lexing.dummy_pos
;;

let dummy_name =
  User (Module.register "<none>", Variable.register "foo")
;;

let dummy_binding k =
  (dummy_name, k, dummy_loc)
;;

let tests: (string * ((unit -> env) -> unit)) list = [
  ("absdefs.mz",
    pass);

  (* Some very simple tests. *)

  ("unbound00.mz", kfail);
  ("unbound01.mz", kfail);
  ("unbound02.mz", kfail);
  ("unbound03.mz", kfail);
  ("unbound04.mz", kfail);
  ("unbound05.mz", kfail);
  ("unbound06.mz", kfail);
  ("unbound07.mz", kfail);
  ("unbound08.mz", kfail);
  ("unbound09.mz", pass);
  ("unbound10.mz", kfail);
  ("unbound11.mz", kfail);
  ("unbound12.mz", kfail);
  ("unbound13.mz", kfail);
  ("unbound14.mz", kfail);
  ("unbound15.mz", kfail);
  ("unbound16.mz", kfail);
  ("unbound17.mz", kfail);
  ("unbound18.mz", kfail);
  ("unbound19.mz", kfail);
  ("unbound20.mz", kfail);
  ("unbound21.mz", pass);
  ("unbound22.mz", kfail);
  ("unbound23.mz", kfail);
  ("unbound24.mz", kfail);
  ("unbound25.mz", kfail);
  ("unbound26.mz", kfail);
  ("unbound27.mz", kfail);
  ("unbound28.mz", kfail);
  ("unbound29.mz", kfail);
  ("unbound30.mz", pass_known_failure);
  ("unbound31.mz", pass_known_failure);
  ("unbound32.mz", kfail);
  ("unbound33.mz", kfail);
  ("unbound34.mz", kfail);
  ("unbound35.mz", kfail);
  ("unbound36.mz", kfail);
  ("unbound37.mz", kfail);
  ("unbound38.mz", kfail);
  ("unbound39.mz", kfail);
  ("unbound40.mz", kfail);
  ("unbound41.mz", kfail);

  ("basic.mz",
    pass);

  ("constructors.mz",
    pass);

  ("dcscope2.mz", kfail);

  ("modules/dcscope.mz", kfail);

  ("constructors_bad_1.mz",
    simple_test (Fail (function MissingField _ -> true | _ -> false)));

  ("constructors_bad_2.mz",
    simple_test (Fail (function ExtraField _ -> true | _ -> false)));

  ("field_access.mz",
    pass);

  ("field_access_bad.mz",
    simple_test (Fail (function NoSuchField _ -> true | _ -> false)));

  ("field_assignment.mz",
    pass);

  ("field_assignment_bad.mz",
    simple_test (Fail (function NoSuchField _ -> true | _ -> false)));

  ("arithmetic.mz", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env ~mname:"int" "int" in
    let foo = point_by_name env "foo" in
    let bar = point_by_name env "bar" in
    check env foo int;
    check env bar int);

  ("atomic.mz",
    pass);
  ("double-release.mz",
    fail);
  ("unwarranted-release.mz",
    fail);

  ("value-restriction-violation.mz",
    fail);
  ("comparison-bug.mz",
    fail);
  ("commutations.mz",
    pass);
  ("forall-wref.mz",
    fail);
  ("consumes-duplicable.mz",
    pass);
  ("consumes-forgotten.mz",
    fail);
  ("permission-shift.mz",
    fail);
  ("permission-shift-duplicable.mz",
    pass);
  ("identity.mz",
    pass);
  ("frame.mz",
    pass);
  ("frame-duplicable.mz",
    pass);
  ("singleton-swap.mz",
    pass);
  ("ref-covariant.mz",
    pass);
  ("deref.mz",
    pass);
  ("deref2.mz",
    pass);
  ("deref3.mz",
    pass);
  ("assign.mz",
    pass);

  ("wrong_type_annotation.mz",
    simple_test (Fail (function ExpectedType _ -> true | _ -> false)));

  ("constraints_in_patterns.mz",
    simple_test (Fail (function ExpectedType _ -> true | _ -> false)));

  ("constraints_in_patterns2.mz",
    pass);

  ("constraints_in_patterns3.mz",
    pass);

  ("constraints_in_patterns4.mz",
    pass);

  ("function.mz", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env ~mname:"int" "int" in
    let foobar = point_by_name env "foobar" in
    check env foobar (tuple [int; int]));

  ("stupid_match.mz",
    simple_test (Fail (function MatchBadDatacon _ -> true | _ -> false)));

  ("value_restriction.mz",
    simple_test (Fail (function NoSuchField _ -> true | _ -> false)));
  ("value_restriction2.mz",
    pass);
  ("value_restriction3.mz",
    pass);
  ("value_restriction4.mz",
    fail);
  ("value_restriction5.mz",
    fail);

  ("variance.mz", fun do_it ->
    let env = do_it () in
    let check_variance n vs =
      let t = find_type_by_name env n in
      if not (get_variance env !!t = vs) then
        failwith "Variances don't match"
    in
    let co = Covariant and contra = Contravariant and bi = Bivariant and inv = Invariant in
    check_variance "list" [co];
    check_variance "ref" [co]; (* yes *)
    check_variance "bi" [bi];
    check_variance "inv" [inv];
    check_variance "test" [co; co; bi];
    check_variance "contra" [contra];
    check_variance "adopts_contra" [contra];
  );

  ("stupid-swap.mz",
    pass
  );

  ("multiple_fields_and_permissions.mz",
    pass
  );

  ("anonargs.mz", pass);

  ("pattern1.mz", pass);

  ("pattern2.mz", pass);

  ("pattern3.mz", pass);

  ("pattern4.mz", pass);

  ("loose_variable.mz", pass);

  ("double-open.mz", pass);

  ("double-open2.mz", pass);

  ("multiple_data_type_groups.mz", pass);

  ("hole.mz", pass);

  ("curry1.mz", pass);

  ("impredicative.mz", pass);

  ("impredicative2.mz", pass);

  ("impredicative3.mz", simple_test (Fail (function
    | ExpectedType _ -> true
    | _ -> false
  )));

  ("impredicative4.mz", simple_test (Fail (function
    | ExpectedType _ -> true
    | _ -> false
  )));

  ("impredicative5.mz", pass);

  ("twostructural.mz", pass);

  (* The merge operation and all its variations. *)

  ("merge1.mz", fun do_it ->
    let env = do_it () in
    let v1 = point_by_name env "v1" in
    check env v1 (concrete (dc env "t" "T") []));

  ("merge2.mz", fun do_it ->
    let env = do_it () in
    let v2 = point_by_name env "v2" in
    let t = TyQ (Exists, dummy_binding KTerm, UserIntroduced,
      TyBar (
        ty_equals v2,
        TyStar (
          TyAnchoredPermission (TyOpen v2,
           concrete
              (dc env "u" "U")
              [FieldValue (Field.register "left", TySingleton (TyBound 0));
               FieldValue (Field.register "right", TySingleton (TyBound 0))]),
          TyAnchoredPermission (
            TyBound 0,
           concrete (dc env "t" "T") []
          )
        )
      ))
    in
    check env v2 t);

  ("merge3.mz", fun do_it ->
    let env = do_it () in
    let v3 = point_by_name env "v3" in
    let t = TyQ (Exists, dummy_binding KTerm, UserIntroduced,
      TyQ (Exists, dummy_binding KTerm, UserIntroduced,
        TyBar (
          ty_equals v3,
          fold_star [
            TyAnchoredPermission (TyOpen v3,
              concrete (dc env "u" "U")
                [FieldValue (Field.register "left", TySingleton (TyBound 0));
                 FieldValue (Field.register "right", TySingleton (TyBound 1))]
            );
            TyAnchoredPermission (
              TyBound 0,
              concrete (dc env "t" "T") []
            );
            TyAnchoredPermission (
              TyBound 1,
              concrete (dc env "t" "T") []
            );
          ]
        )))
    in
    check env v3 t);

  ("merge4.mz", fun do_it ->
    let env = do_it () in
    let v4 = point_by_name env "v4" in
    let w = find_type_by_name env "w" in
    let int = find_type_by_name env ~mname:"int" "int" in
    let t = TyApp (w, [int]) in
    check env v4 t);

  ("merge5.mz", fun do_it ->
    let env = do_it () in
    let v5 = point_by_name env "v5" in
    let v = find_type_by_name env "v" in
    let int = find_type_by_name env ~mname:"int" "int" in
    let t = TyApp (v, [int; int]) in
    check env v5 t);

  ("merge6.mz", pass);

  ("merge7.mz", pass);

  ("merge8.mz", fun do_it ->
    let env = do_it () in
    let v8 = point_by_name env "v8" in
    let v = find_type_by_name env "v" in
    let t = TyQ (Forall, dummy_binding KType, UserIntroduced,
        TyApp (v, [TyBound 0; TyBound 0])
      )
    in
    check env v8 t);

  ("merge9.mz", fun do_it ->
    let env = do_it () in
    let v9 = point_by_name env "v9" in
    let ref = find_type_by_name env "ref" in
    let int = find_type_by_name env ~mname:"int" "int" in
    let t = TyApp (ref, [int]) in
    check env v9 t);

  ("merge10.mz", fun do_it ->
    let env = do_it () in
    let v10 = point_by_name env "v10" in
    let foo = find_type_by_name env "foo" in
    let t = find_type_by_name env "t" in
    let t = TyApp (foo, [t]) in
    check env v10 t);

  ("merge11.mz", fun do_it ->
    let env = do_it () in
    let v11 = point_by_name env "v11" in
    let ref = find_type_by_name env "ref" in
    let int = find_type_by_name env ~mname:"int" "int" in
    let t = TyApp (ref, [TyApp (ref, [int])]) in
    check env v11 t);

  ("merge12.mz", fun do_it ->
    let env = do_it () in
    let v12 = point_by_name env "v12" in
    let int = find_type_by_name env ~mname:"int" "int" in
    (* Urgh, have to input internal syntax to check function types... maybe we
     * should write surface syntax here and have it simplified by the desugar
     * procedure? ... *)
    let t = TyQ (Forall, dummy_binding KTerm, UserIntroduced, TyArrow (
      TyBar (
        TySingleton (TyBound 0),
        TyAnchoredPermission (TyBound 0, int)
      ), int))
    in
    check env v12 t);

  ("merge13.mz", fun do_it ->
    let env = do_it () in
    let v13 = point_by_name env "v13" in
    let x = point_by_name env "x" in
    let int = find_type_by_name env ~mname:"int" "int" in
    let t = find_type_by_name env "t" in
    let t = TyApp (t, [int]) in
    check env v13 t;
    check env x int);

  ("merge14.mz", fun do_it ->
    let env = do_it () in
    let v14 = point_by_name env "v14" in
    let int = find_type_by_name env ~mname:"int" "int" in
    let t = find_type_by_name env "t" in
    (* Look at how fancy we used to be when we had singleton-subtyping! *)
    (* let t = TyQ (Exists, dummy_binding KTerm, UserIntroduced, TyBar (
      TyApp (t, [TySingleton (TyBound 0)]),
      TyAnchoredPermission (TyBound 0, int)
    )) in *)
    let t = TyApp (t, [int]) in
    check env v14 t);

  ("merge15.mz", pass);

  ("merge16.mz", pass);

  ("merge18.mz", pass);

  ("merge19.mz", pass);

  ("merge20.mz", pass);

  ("merge_generalize_val.mz", pass);

  ("merge-funcs.mz", pass_known_failure);

  ("constraints_merge.mz",
    simple_test ~warn_error:pedantic_warn_error Pass);

  (* Resource allocation conflicts. *)

  ("conflict2.mz",
    simple_test ~warn_error:pedantic_warn_error Pass);

  (* Marking environments as inconsistent. *)

  ("inconsistent1.mz",
    pass
  );

  ("inconsistent2.mz",
    pass
  );

  (* Singleton types. *)

  ("singleton1.mz", fun do_it ->
    let env = do_it () in
    let x = point_by_name env "x" in
    let s1 = point_by_name env "s1" in
    let t = find_type_by_name env "t" in
    (* We have to perform a syntactic comparison here, otherwise [check] which
     * uses [sub] under the hood might implicitly perform the
     * singleton-subtyping-rule -- this would defeat the whole purpose of the
     * test. *)
    let perms = get_permissions env x in
    if List.exists (FactInference.is_exclusive env) perms then
      failwith "The permission on [x] should've been consumed";
    let perms = get_permissions env s1 in
    if not (List.exists ((=) (TyApp (t, [concrete (dc env "t" "A") []]))) perms) then
      failwith "The right permission was not extracted for [s1].";
  );

  ("singleton2.mz", pass);

  (* Duplicity constraints. *)

  ("duplicity1.mz", pass);
  ("duplicity2.mz", pass);
  ("dup.mz", fail);
  ("dup2.mz", pass);

  (* Polymorphic function calls *)

  ("polycall1.mz",
    simple_test (Fail (function IllKindedTypeApplication _ -> true | _ -> false)));

  ("polycall2.mz",
    simple_test (Fail (function BadTypeApplication _ -> true | _ -> false)));

  ("polycall3.mz",
    simple_test ~warn_error:pedantic_warn_error Pass);

  ("polycall4.mz",
    simple_test ~warn_error:pedantic_warn_error Pass);

  ("polycall5.mz",
    simple_test ~warn_error:pedantic_warn_error Pass);

  ("polycall6.mz",
    simple_test ~warn_error:pedantic_warn_error Pass);

  (* Tests are expected to fail. *)

  ("fail1.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail2.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail3.mz",
    simple_test ((Fail (function NoSuchField _ -> true | _ -> false))));

  ("fail4.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail5.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail6.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail7.mz", kfail);

  ("fail8.mz",
    simple_test ((Fail (function BadPattern _ -> true | _ -> false))));

  ("fail9.mz",
    simple_test ((Fail (function NotDynamic _ -> true | _ -> false))));

  ("fail10.mz",
    simple_test ((Fail (function BadField _ -> true | _ -> false))));

  ("fail11.mz", kfail);

  (* Adoption. *)

  ("adopts1.mz",
    pass);

  ("adopts2.mz",
    simple_test (Fail (function NonExclusiveAdoptee _ -> true | _ -> false)));

  ("adopts3.mz", kfail);

  ("adopts4.mz",
    simple_test (Fail (function NonExclusiveAdoptee _ -> true | _ -> false)));

  ("adopts5.mz",
    pass);

  ("adopts6.mz",
    pass);

  ("adopts7.mz",
    pass);

  ("adopts8.mz",
    simple_test (Fail (function NonExclusiveAdoptee _ -> true | _ -> false)));

  ("adopts9.mz",
    pass);

  ("adopts10.mz",
    simple_test (Fail (function NotMergingClauses _ -> true | _ -> false)));

  ("adopts11.mz", pass_known_failure);
  ("adopts12.mz",
    pass);

  ("adopts13.mz", fail);
  ("adopts14.mz", fail);
  ("adopts15.mz", pass);
  ("adopts16.mz", pass);
  ("adopts17.mz", pass);
  ("adopts18.mz", pass);
  ("adopts19.mz", pass);

  (* Bigger examples. *)

  ("list-length.mz", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env ~mname:"int" "int" in
    let zero = point_by_name env "zero" in
    check env zero int);

  ("list-length-variant.mz", pass);

  ("list-concat.mz", pass);
  ("icfp.mz", pass);

  ("list-concat-dup.mz",
    pass
  );

  ("list-length.mz",
    pass
  );

  ("list-map0.mz",
    pass
  );

  ("list-map1.mz",
    pass
  );

  ("list-map2.mz",
    pass
  );

  ("list-map3.mz",
    pass
  );

  ("list-map-tail-rec.mz",
    pass
  );

  ("list-rev.mz",
    pass
  );

  ("list-find.mz",
    pass
  );

  ("list-mem2.mz",
    pass
  );

  ("list-id.mz",
    pass
  );

  ("xlist-copy.mz",
    pass
  );

  ("xlist-concat.mz",
    pass
  );

  ("xlist-concat1.mz",
    pass
  );

  ("xlist-concat2.mz",
    pass
  );

  ("tree_size.mz",
    pass
  );

  ("in_place_traversal.mz",
    pass
  );

  ("counter.mz",
    pass
  );

  ("xswap.mz",
    pass
  );

  ("bag_lifo.mz", pass);

  ("bag_fifo.mz", pass);

  ("union-find-nesting.mz", pass);
  ("union-find-dynamic.mz", pass);

  ("modules/simple.mz", pass);

  ("modules/simple2.mz", simple_test (Fail (function
    | DataTypeMismatchInSignature _ -> true | _ -> false
  )));

  ("modules/m.mz", pass);

  ("modules/exporttwo.mz", pass);

  ("modules/qualified.mz", pass);

  ("modules/equations_in_mzi.mz", pass);

  ("modules/export_nondup.mz",
    simple_test (Fail (function ExportNotDuplicable _ -> true | _ -> false)));

  ("missing-export.mz", kfail);

  ("weird-datacon-shadowing.mz", kfail_known_failure);

  ("assert.mz", pass);
  ("assert2.mz", fail);

  ("priority.mz", pass);

  ("fieldEvaluationOrder.mz", pass);

  ("fieldEvaluationOrderReject1.mz", fail);

  ("fieldEvaluationOrderReject2.mz", fail);

  ("monads.mz", pass);

  ("adopts-non-mutable-type.mz", simple_test (Fail (function NonExclusiveAdoptee _ -> true | _ -> false)));

  ("adopts-type-variable.mz", pass);

  ("ref-confusion.mz", kfail);

  ("strip_floating_perms.mz", simple_test (Fail (function ExpectedType _ -> true | _ -> false)));

  ("fact-inconsistency.mz", pass);

  ("dfs-simple.mz", pass);

  ("dfs-owns.mz", pass);

  ("dfs-example.mz", pass);

  ("owns1.mz", pass);

  ("owns2.mz", simple_test (Fail (function NotDynamic _ -> true | _ -> false)));

  ("owns3.mz", pass);

  ("tuple-syntax.mz", pass);

  ("same-type-var-bug.mz", kfail);

  ("assert-bug.mz", pass);

  ("function-comparison.mz", pass);

  ("function-comparison2.mz", fail);

  ("masking.mz", fail);

  ("masking2.mz", fail);

  ("masking3.mz", pass);

  ("bad-linearity.mz", fail);

  ("bad-generalization.mz", fail);

  ("bad-levels.mz", fail);

  ("dup-value.mzi", kfail);

  ("dup-datacon.mzi", kfail);

  ("unqualified-datacon.mz", kfail);

  ("improve-inference.mz", pass);
  ("improve-inference2.mz", pass);

  ("cps-dereliction.mz", pass);

  ("fold-permission.mz", pass);

  ("abstract.mz", pass);

  ("abstract2.mz", simple_test (Fail (function
    | DataTypeMismatchInSignature _ -> true | _ -> false
  )));

  ("ref-swap.mz", pass);

  ("multiple-match-ref.mz", fail);

  ("018.mz", pass);

  ("vicious-cycle.mz", pass);

  ("cycle1.mz", pass);  (* circular dependency between the modules, detected only at link time by ocaml *)
  ("cyclic1.mz", fail); (* circular dependency between the interfaces, detected at type-checking time by mezzo *)

  ("named-tuple-components.mz", pass);

  ("abstract-perm.mz", pass);

  ("dup_sign.mz", simple_test (Fail (function NoSuchTypeInSignature _ -> true | _ -> false)));
  ("dup_sign1.mz", pass);
  ("dup_sign2.mz", fail);
  ("dup_sign3.mz", pass);
  ("dup_sign4.mz", pass);
  ("dup_sign5.mz", fail);

  ("tableau.mz", pass);
  ("smemoize.mz", pass);
  ("use-magic.mz", pass);
  ("list2array.mz", pass);
  ("sub_constraints_nonpoint_type.mz", pass);
  ("merge-tyapp-with-two-subs.mz", pass);

  ("exist00.mz", pass);
  ("exist01.mz", pass);
  ("exist03.mz", pass);
  ("exist04.mz", pass);
  ("exist05.mz", pass);
  ("exist06.mz", pass);
  ("exist07.mz", pass);
  ("exist08.mz", pass);
  ("exist09.mz", pass);

  ("exists-tyapp.mz", pass);
  ("exists-tyapp2.mz", fail);

  ("bad-arity.mz", simple_test (Fail (function BadPattern _ -> true | _ -> false)));
  ("bad-arity2.mz", simple_test (Fail (function BadPattern _ -> true | _ -> false)));
  ("dependent-type.mz", pass);
  ("caires_seco_node.mz", pass);
  ("persistentarray_nesting.mz", pass);
  ("bad-variance-annot.mz", simple_test (Fail (function VarianceAnnotationMismatch -> true | _ -> false)));
  ("bad-variance-annot2.mz", simple_test (Fail (function DataTypeMismatchInSignature _ -> true | _ -> false)));
  ("array-covariance.mz", pass);
  ("array-contravariance.mz", fail);
  ("array-focus.mz", fail);
  ("queue_nesting.mz", fail);
  ("queue_nesting2.mz", fail);
  ("take-abstract.mz", fail);
  ("overflow.mz", fail);
  ("facts.mz", pass);
  ("facts00.mz", fail);
  ("facts01.mz", fail);
  ("facts02.mz", fail);
  ("facts03.mz", fail);
  ("facts04.mz", fail);
  ("facts05.mz", kfail);
  ("facts06.mz", pass);
  ("facts07.mz", fail);
  ("facts08.mz", fail);
  ("facts09.mz", fail);
  ("facts10.mz", fail);
  ("facts11.mz", pass_known_failure);
  ("data-term.mz", pass_known_failure);
  ("fact-term.mz", fail_known_failure);

  ("local-type.mz", pass);
  ("local-type2.mz", pass_known_failure);
  ("local-type3.mz", pass_known_failure);
  ("local-type4.mz", pass);
  ("tyapp.mz", pass);
  ("tyand00.mz", kfail);
  ("tyand01.mz", pass);
  ("tyand02.mz", pass);
  ("tyand03.mz", fail);
  ("tyand04.mz", pass);
  ("tyand05.mz", fail);
  ("tyand06.mz", fail);
  ("incorrect-fields.mz", kfail);
  ("name-intro.mz", pass);
  ("name-intro2.mz", pass);
  ("name-intro3.mz", pass_known_failure);
  ("name-intro4.mz", pass);
  ("name-intro5.mz", pass);
  ("desugaring00.mz", pass);
  ("exists-forall.mz", pass);
  ("name-capture.mz", pass);
  ("time.mz", pass);
  ("cps-old.mz", pass);
  ("delimcc.mz", pass);
  ("cps.mz", pass);
  ("miterator.mz", pass);
  ("call.mz", pass);
  ("tree-removal.mz", pass);
  ("pattern-sharing.mz", fail);
  ("gadt.mz", pass);
  ("gadt-bug.mz", fail_known_failure);
  ("abbrev-1.mz", pass);
  ("abbrev-2.mz", pass);
  ("abbrev-3.mz", pass);
  ("abbrev-4.mz", pass);
  ("existential-witness.mz", pass);
  ("residual.mz", pass);
  ("quantifier-bug.mz", fail_known_failure);
  ("eta.mz", pass);
  ("array-1.mz", pass);
  ("array-2.mz", fail);
  ("array-3.mz", fail);
  ("export-names.mz", pass);
  ("double-datacon.mz", kfail);
  ("datacon-shadow.mz", fail);
  ("self.mz", fail);
  ("fractional.mzi", pass); (* no implementation, for now *)
  ("vide.mz", pass);
  ("openvide.mz", pass);
  ("exclusive-bug.mz", pass);
  ("dynarray.mz", pass);
  ("while-1.mz", pass);
  ("while-2.mz", fail);
  ("while-3.mz", pass);
  ("species.mz", pass);
  ("ghost00.mz", kfail);
  ("ifthen-bug.mz", pass);
  ("magic-map.mz", pass);
  ("exist-name-conflict.mz", pass);
  ("assert-point.mz", pass);
  ("named-return.mz", pass);
  ("named-return2.mz", pass);
  ("incorrect-interface.mz", fail);
  ("instantiate_exists.mz", pass);
  ("bind-op.mz", pass);
  ("letflex.mz", pass);
  ("pack1.mz", pass);
  ("pack2.mz", pass);
  ("landin.mz", pass);
  ("strange.mz", fail);
  ("localtype1.mz", pass);
  ("localtype2.mz", pass);
  ("covariantlock.mz", pass);
  ("pack-assert.mz", pass_known_failure);
  ("oneshot-test.mz", fail);
  ("sparray.mz", pass);
  ("interface-arg-name.mz", pass_known_failure);
  ("tree-coroutine.mz", pass);
  ("tree-coroutine-disposable-ack.mz", pass);
  ("concurrentsort.mz", pass);
  ("derived_locks.mz", pass);
  ("rich-bool1.mz", pass_known_failure);
  ("frame-wand.mz", pass_known_failure);
  ("iteration.mz", pass);
  ("fpiterator-focused.mz", pass); (* very costly, sorry *)
  ("flexible-point.mz", pass);
  ("assert-exists.mz", pass);

  (* The tests below are intentionally not run as they cause the type-checker to
   * loop. We still want to list them as, eventually, we will want to fix them. *)
  ("landin-variant.mz", fun _ -> raise KnownFailure);
  ("cyclic-list.mz", fun _ -> raise KnownFailure);
  ("diverge.mz", fun _ -> raise KnownFailure);
];;

let mz_files_in_directory (dir : string) : string list =
  let filenames = Array.to_list (Sys.readdir dir) in
  List.filter (fun filename ->
    Filename.check_suffix filename ".mz"
  ) filenames

let tests_in_directory dir =
  List.map (fun filename ->
    filename, pass
  ) (mz_files_in_directory (Configure.root_dir ^ "/" ^ dir))

let corelib_tests: (string * ((unit -> env) -> unit)) list =
  tests_in_directory "corelib"
;;

let stdlib_tests: (string * ((unit -> env) -> unit)) list =
  tests_in_directory "stdlib"
;;

let interpreter_tests =
  tests_in_directory "tests/interpreter"

type result =
| WasNotRun
| Success
| Failure

let run_one_test_raw name (f: result ref -> unit): result * string =
  let open Bash in
  (* This function is intended to be possibly run in a separate
     process. Avoid side effects (global variables, printing, etc.). *)
  Log.warn_count := 0;
  let buf = Buffer.create 1024 in
  let result = ref WasNotRun in
  let () =
    try
      f result;
      Printf.bprintf buf "%s✓ %s%s"
        colors.green colors.default name;
      if !Log.warn_count > 0 then
        Printf.bprintf buf ", %s%d%s warning%s"
          colors.red !Log.warn_count colors.default
          (if !Log.warn_count > 1 then "s" else "");
      Printf.bprintf buf "\n"
    with
    | KnownFailure ->
        Printf.bprintf buf "%s! %s%s\n" colors.orange colors.default name
    | _ as e ->
        result := Failure;
        Printf.bprintf buf "%s✗ %s%s\n%s\n%s"
          colors.red colors.default name
          (Printexc.to_string e)
          (Printexc.get_backtrace())
  in
  !result, Buffer.contents buf

let run_one_test prefix (file, test) : result * string =
  TypeErrors.parse_warn_error silent_warn_error;
  run_one_test_raw file (fun result ->
    test (fun () ->
      result := Success;
      Driver.process (Filename.concat prefix file)
    );
  )

let run_one_unit_test (name, (f, known_failure, outcome)) =
  run_one_test_raw name (fun result ->
    simple_test ?known_failure outcome (fun () ->
      result := Success;
      f ()
  ))

(* Total number of tests. *)
let count = ref 0
(* Number of tests actually run. *)
let do_it_count = ref 0
(* Number of tests considered failed (not counting known failures). *)
let failed = ref 0
(* Names of tests considered failed. *)
let names_failed = ref []

(* [acknowledge] is invoked in the master process when a test finishes. *)
let acknowledge ((file, _), ()) (result, output) =
  incr count;
  print_string output;
  flush stdout;
  begin match result with
  | WasNotRun ->
      ()
  | Success ->
      incr do_it_count
  | Failure ->
      incr do_it_count;
      incr failed;
      names_failed := file :: !names_failed
  end;
  (* An empty list means, no new tasks. *)
  []

(* [run] runs a bunch of tests in parallel. *)
let run worker tests : unit =
  Functory.Cores.set_number_of_cores 4;
  Functory.Cores.compute
    ~worker
    ~master:acknowledge
    tests

let run_files prefix tests : unit =
  let worker = run_one_test prefix in
  let tests = List.map (fun x -> x, ()) tests in
  run worker tests

let run_unit_tests () : unit =
  let worker = run_one_unit_test in
  let tests = UnitTests.unit_tests in
  let tests = List.map (fun x -> x, ()) tests in
  run worker tests

let () =
  let open Bash in
  Driver.add_include_dir (Filename.concat Configure.root_dir "corelib");
  Driver.add_include_dir (Filename.concat Configure.root_dir "stdlib");
  let center s =
    let l = String.length s in
    let padding = String.make ((Bash.twidth - l) / 2) ' ' in
    Printf.printf "\n%s%s\n\n%!" padding s;
  in

  (* Check the core modules. *)
  center "~[ Core Modules ]~";
  run_files "corelib/" corelib_tests;

  (* Check the standard library modules. *)
  center "~[ Standard Library Modules ]~";
  run_files "stdlib/" stdlib_tests;

  (* Check the interpreter tests. *)
  center "~[ Interpreter Tests ]~";
  run_files "tests/interpreter/" interpreter_tests;

  (* Unit tests. *)
  center "~[ Hand-written Unit Tests ]~";
  run_unit_tests ();

  (* Thrash the include path, and then do the unit tests. *)
  Options.no_auto_include := true;
  Driver.add_include_dir "tests";
  Driver.add_include_dir "tests/modules";
  center "~[ Unit Tests ]~";
  run_files "tests/" tests;

  Printf.printf "%s%d%s tests listed (%d tests actually run), "
    colors.blue !count colors.default !do_it_count;
  if !failed > 0 then
    let names_failed =
      match !names_failed with
      | [] ->
          assert false
      | hd :: [] ->
          hd
      | hd :: tl ->
          String.concat ", " (List.rev tl) ^ " and " ^ hd
    in
    Printf.printf "%s%d unexpected failure%s (namely: %s), this is BAD!%s\n"
      colors.red
      !failed (if !failed > 1 then "s" else "")
      names_failed
      colors.default
  else
    Printf.printf "%sall passed%s, congratulations.\n" colors.green colors.default
;;
