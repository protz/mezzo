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

open Types
open TypeChecker
open TestUtils
open TypeErrors

let check env point t =
  ignore (check_return_type env point t)
;;

let point_by_name env ?mname name =
  point_by_name env ?mname (Variable.register name)
;;

type outcome =
  (* Fail at kind-checking time. *)
  | KFail of (KindCheck.raw_error -> bool)
  (* Fail at type-checking time. *)
  | Fail of (raw_error -> bool)
  | Pass

let simple_test ?(pedantic=false) outcome = fun do_it ->
  try
    Options.pedantic := pedantic;
    ignore (do_it ());
    match outcome with
    | KFail _ ->
        raise (Failure "Test passed, it was supposed to fail")
    | Fail _ ->
        raise (Failure "Test passed, it was supposed to fail")
    | Pass ->
        ();
  with
  | TypeCheckerError (_, e) ->
      begin match outcome with
      | Pass ->
          raise (Failure "Test failed, it was supposed to pass")
      | Fail f ->
          if f e then
            ()
          else
            raise (Failure "Test failed but not for the right reason")
      | KFail _ ->
          raise (Failure "Test failed but not for the right reason")
      end

  | K.KindError (_, e) ->
      begin match outcome with
      | Pass ->
          raise (Failure "Test failed, it was supposed to pass")
      | KFail f ->
          if f e then
            ()
          else
            raise (Failure "Test failed but not for the right reason")
      | Fail _ ->
          raise (Failure "Test failed but not for the right reason")
      end
;;

let dummy_loc =
  Lexing.dummy_pos, Lexing.dummy_pos
;;

let dummy_name =
  User (Module.register "<none>", Variable.register "foo")
;;

let edummy_binding k =
  dummy_name, k, dummy_loc
;;

let dummy_binding k =
  (dummy_name, k, dummy_loc), CanInstantiate
;;

let tests: (string * ((unit -> env) -> unit)) list = [
  (* Put the core definitions first, so that if it fails, we can see it
   * immediately. *)

  ("pervasives.mz",
    simple_test Pass);

  ("absdefs.mz",
    simple_test Pass);

  (* Some very simple tests. *)

  ("basic.mz",
    simple_test Pass);

  ("constructors.mz",
    simple_test Pass);

  ("dcscope2.mz",
    simple_test (KFail (function K.UnboundDataConstructor _ -> true | _ -> false)));

  ("modules/dcscope.mz",
    simple_test (KFail (function K.UnboundDataConstructor _ -> true | _ -> false)));

  ("constructors_bad_1.mz",
    simple_test (Fail (function MissingField _ -> true | _ -> false)));

  ("constructors_bad_2.mz",
    simple_test (Fail (function ExtraField _ -> true | _ -> false)));

  ("field_access.mz",
    simple_test Pass);

  ("field_access_bad.mz",
    simple_test (Fail (function NoSuchField _ -> true | _ -> false)));

  ("field_assignment.mz",
    simple_test Pass);

  ("field_assignment_bad.mz",
    simple_test (Fail (function NoSuchField _ -> true | _ -> false)));

  ("arithmetic.mz", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let foo = point_by_name env "foo" in
    let bar = point_by_name env "bar" in
    check env foo int;
    check env bar int);

  ("wrong_type_annotation.mz",
    simple_test (Fail (function ExpectedType _ -> true | _ -> false)));

  ("constraints_in_patterns.mz",
    simple_test (Fail (function ExpectedType _ -> true | _ -> false)));

  ("constraints_in_patterns2.mz",
    simple_test Pass);

  ("constraints_in_patterns3.mz",
    simple_test Pass);

  ("constraints_in_patterns4.mz",
    simple_test Pass);

  ("function.mz", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let foobar = point_by_name env "foobar" in
    check env foobar (tuple [int; int]));

  ("stupid_match.mz",
    simple_test (Fail (function MatchBadDatacon _ -> true | _ -> false)));

  ("value_restriction.mz",
    simple_test (Fail (function NoSuchField _ -> true | _ -> false)));

  ("variance.mz", fun do_it ->
    let env = do_it () in
    let check_variance n vs =
      let t = find_type_by_name env n in
      match find_type env !!t with
      | _, { definition = Some (_, vs'); _ } when vs = vs' ->
          ()
      | _ ->
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
    simple_test Pass
  );

  ("multiple_fields_and_permissions.mz",
    simple_test Pass
  );

  ("anonargs.mz", simple_test Pass);

  ("pattern1.mz", simple_test Pass);

  ("pattern2.mz", simple_test Pass);

  ("pattern3.mz", simple_test Pass);

  ("pattern4.mz", simple_test Pass);

  ("loose_variable.mz", simple_test Pass);

  ("multiple_data_type_groups.mz", simple_test Pass);

  ("curry1.mz", simple_test Pass);

  ("impredicative.mz", simple_test Pass);

  ("impredicative2.mz", simple_test Pass);

  ("impredicative3.mz", simple_test (Fail (function
    | ExpectedType _ -> true
    | _ -> false
  )));

  ("impredicative4.mz", simple_test (Fail (function
    | ExpectedType _ -> true
    | _ -> false
  )));

  ("impredicative5.mz", simple_test Pass);

  ("twostructural.mz", simple_test Pass);

  (* The merge operation and all its variations. *)

  ("merge1.mz", fun do_it ->
    let env = do_it () in
    let v1 = point_by_name env "v1" in
    check env v1 (TyConcreteUnfolded (Datacon.register "T", [], ty_bottom)));

  ("merge2.mz", fun do_it ->
    let env = do_it () in
    let v2 = point_by_name env "v2" in
    let t = TyExists (edummy_binding KTerm,
      TyBar (
        ty_equals v2,
        TyStar (
          TyAnchoredPermission (TyPoint v2,
            TyConcreteUnfolded (Datacon.register "U",
              [FieldValue (Field.register "left", TySingleton (TyVar 0));
               FieldValue (Field.register "right", TySingleton (TyVar 0))], ty_bottom)),
          TyAnchoredPermission (
            TyVar 0,
            TyConcreteUnfolded (Datacon.register "T", [], ty_bottom)
          )
        )
      ))
    in
    check env v2 t);

  ("merge3.mz", fun do_it ->
    let env = do_it () in
    let v3 = point_by_name env "v3" in
    let t = TyExists (edummy_binding KTerm,
      TyExists (edummy_binding KTerm,
        TyBar (
          ty_equals v3,
          fold_star [
            TyAnchoredPermission (TyPoint v3,
              TyConcreteUnfolded (Datacon.register "U",
                [FieldValue (Field.register "left", TySingleton (TyVar 0));
                 FieldValue (Field.register "right", TySingleton (TyVar 1))],
                 ty_bottom));
            TyAnchoredPermission (
              TyVar 0,
              TyConcreteUnfolded (Datacon.register "T", [], ty_bottom)
            );
            TyAnchoredPermission (
              TyVar 1,
              TyConcreteUnfolded (Datacon.register "T", [], ty_bottom)
            );
          ]
        )))
    in
    check env v3 t);

  ("merge4.mz", fun do_it ->
    let env = do_it () in
    let v4 = point_by_name env "v4" in
    let w = find_type_by_name env "w" in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let t = TyApp (w, [int]) in
    check env v4 t);

  ("merge5.mz", fun do_it ->
    let env = do_it () in
    let v5 = point_by_name env "v5" in
    let v = find_type_by_name env "v" in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let t = TyApp (v, [int; int]) in
    check env v5 t);

  ("merge6.mz", fun do_it ->
    let env = do_it () in
    let v6 = point_by_name env "v6" in
    let v = find_type_by_name env "v" in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let t = TyForall (dummy_binding KType,
      TyApp (v, [int; TyVar 0])
    )
    in
    check env v6 t);

  ("merge7.mz", fun do_it ->
    let env = do_it () in
    let v7 = point_by_name env "v7" in
    let v = find_type_by_name env "v" in
    let t = TyForall (dummy_binding KType,
      TyForall (dummy_binding KType,
        TyApp (v, [TyVar 1; TyVar 0])
      ))
    in
    check env v7 t);

  ("merge8.mz", fun do_it ->
    let env = do_it () in
    let v8 = point_by_name env "v8" in
    let v = find_type_by_name env "v" in
    let t = TyForall (dummy_binding KType,
        TyApp (v, [TyVar 0; TyVar 0])
      )
    in
    check env v8 t);

  ("merge9.mz", fun do_it ->
    let env = do_it () in
    let v9 = point_by_name env "v9" in
    let ref = find_type_by_name env "ref" in
    let int = find_type_by_name env ~mname:"Core" "int" in
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
    let int = find_type_by_name env ~mname:"Core" "int" in
    let t = TyApp (ref, [TyApp (ref, [int])]) in
    check env v11 t);

  ("merge12.mz", fun do_it ->
    let env = do_it () in
    let v12 = point_by_name env "v12" in
    let int = find_type_by_name env ~mname:"Core" "int" in
    (* Urgh, have to input internal syntax to check function types... maybe we
     * should write surface syntax here and have it simplified by the desugar
     * procedure? ... *)
    let t = TyForall (dummy_binding KTerm, TyArrow (
      TyBar (
        TySingleton (TyVar 0),
        TyAnchoredPermission (TyVar 0, int)
      ), int))
    in
    check env v12 t);

  ("merge13.mz", fun do_it ->
    let env = do_it () in
    let v13 = point_by_name env "v13" in
    let x = point_by_name env "x" in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let t = find_type_by_name env "t" in
    let t = TyApp (t, [int]) in
    check env v13 t;
    check env x int);

  ("merge14.mz", fun do_it ->
    let env = do_it () in
    let v14 = point_by_name env "v14" in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let t = find_type_by_name env "t" in
    (* Look at how fancy we used to be when we had singleton-subtyping! *)
    (* let t = TyExists (edummy_binding KTerm, TyBar (
      TyApp (t, [TySingleton (TyVar 0)]),
      TyAnchoredPermission (TyVar 0, int)
    )) in *)
    let t = TyApp (t, [int]) in
    check env v14 t);

  ("merge15.mz", simple_test Pass);

  ("merge16.mz", simple_test Pass);

  ("merge18.mz", simple_test Pass);

  ("merge19.mz", simple_test Pass);

  ("merge_generalize_val.mz", fun do_it ->
    let env = do_it () in
    let x = point_by_name env "x" in
    let y = point_by_name env "y" in
    let z = point_by_name env "z" in
    let u = find_type_by_name env "u" in
    let t = TyForall (dummy_binding KType, TyApp (u, [TyVar 0])) in
    check env x t;
    check env y t;
    check env z t;
  );

  ("constraints_merge.mz",
    simple_test ~pedantic:true Pass);

  (* Resource allocation conflicts. *)

  ("conflict1.mz",
    simple_test
      ~pedantic:true
      ((Fail (function ResourceAllocationConflict _ -> true | _ -> false)))
  );

  ("conflict2.mz",
    simple_test ~pedantic:true Pass);

  (* Singleton types. *)

  ("singleton1.mz", fun do_it ->
    Options.pedantic := false;
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
    if not (List.exists ((=) (TyApp (t, [datacon "A" []]))) perms) then
      failwith "The right permission was not extracted for [s1].";
  );

  (* Doesn't pass anymore since we removed singleton-subtyping! *)
  (* ("singleton2.mz", simple_test Pass); *)

  (* Marking environments as inconsistent. *)

  ("inconsistent1.mz",
    simple_test Pass
  );

  ("inconsistent2.mz",
    simple_test Pass
  );

  (* Duplicity constraints. *)

  ("duplicity1.mz",
    simple_test Pass
  );

  ("duplicity2.mz",
    simple_test Pass
  );

  (* Polymorphic function calls *)

  ("polycall1.mz",
    simple_test (Fail (function IllKindedTypeApplication _ -> true | _ -> false)));

  ("polycall2.mz",
    simple_test (Fail (function BadTypeApplication _ -> true | _ -> false)));

  ("polycall3.mz",
    simple_test ~pedantic:true Pass);

  ("polycall4.mz",
    simple_test ~pedantic:true Pass);

  ("polycall5.mz",
    simple_test ~pedantic:true Pass);

  ("polycall6.mz",
    simple_test ~pedantic:true Pass);

  (* Tests are expected to fail. *)

  ("fail1.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail2.mz",
    simple_test ((Fail (function ExpectedType _ -> true | _ -> false))));

  ("fail3.mz",
    simple_test ((Fail (function NoSuchField _ -> true | _ -> false))));

  ("fail4.mz",
    simple_test ((Fail (function NoSuchPermission _ -> true | _ -> false))));

  ("fail5.mz",
    simple_test ((Fail (function NoSuchPermission _ -> true | _ -> false))));

  ("fail6.mz",
    simple_test ((Fail (function NoSuchPermission _ -> true | _ -> false))));

  ("fail7.mz",
    simple_test ((Fail (function FieldMismatch _ -> true | _ -> false))));

  ("fail8.mz",
    simple_test ((Fail (function BadPattern _ -> true | _ -> false))));

  (* Adoption. *)

  ("adopts1.mz",
    simple_test Pass);

  ("adopts2.mz",
    simple_test (Fail (function BadFactForAdoptedType _ -> true | _ -> false)));

  ("adopts3.mz",
    simple_test (KFail (function K.AdopterNotExclusive _ -> true | _ -> false)));

  ("adopts4.mz",
    simple_test (Fail (function BadFactForAdoptedType _ -> true | _ -> false)));

  ("adopts5.mz",
    simple_test Pass);

  ("adopts6.mz",
    simple_test Pass);

  ("adopts7.mz",
    simple_test Pass);

  ("adopts8.mz",
    simple_test (Fail (function BadFactForAdoptedType _ -> true | _ -> false)));

  ("adopts9.mz",
    simple_test Pass);

  ("adopts10.mz",
    simple_test (Fail (function NotMergingClauses _ -> true | _ -> false)));

  ("adopts12.mz",
    simple_test Pass);

  (* Bigger examples. *)

  ("list-length.mz", fun do_it ->
    let env = do_it () in
    let int = find_type_by_name env ~mname:"Core" "int" in
    let zero = point_by_name env "zero" in
    check env zero int);

  ("list-length-variant.mz", simple_test Pass);

  ("list-concat.mz", fun do_it ->
    let env = do_it () in
    let x = point_by_name env "x" in
    let list = find_type_by_name env "list" in
    let t = TyForall (dummy_binding KType,
      TyApp (list, [TyVar 0])
    ) in
    check env x t);

  ("list-concat-dup.mz",
    simple_test Pass
  );

  ("list-length.mz",
    simple_test Pass
  );

  ("list-map0.mz",
    simple_test Pass
  );

  ("list-map1.mz",
    simple_test Pass
  );

  ("list-map2.mz",
    simple_test Pass
  );

  ("list-map3.mz",
    simple_test Pass
  );

  ("list-map4.mz",
    simple_test Pass
  );

  ("list-rev.mz",
    simple_test Pass
  );

  ("list-find.mz",
    simple_test Pass
  );

  ("list-mem2.mz",
    simple_test Pass
  );

  ("list-id.mz",
    simple_test Pass
  );

  ("xlist-copy.mz",
    simple_test Pass
  );

  ("xlist-concat.mz",
    simple_test Pass
  );

  ("xlist-concat1.mz",
    simple_test Pass
  );

  ("xlist-concat2.mz",
    simple_test Pass
  );

  ("tree_size.mz",
    simple_test Pass
  );

  ("in_place_traversal.mz",
    simple_test Pass
  );

  ("counter.mz",
    simple_test Pass
  );

  ("xswap.mz",
    simple_test Pass
  );

  ("bag_lifo.mz", simple_test Pass);

  ("bag_fifo.mz", simple_test Pass);

  (* ("landin.mz", simple_test Pass); *)

  ("modules/simple.mz", simple_test Pass);

  ("modules/simple2.mz", simple_test (Fail (function
    | DataTypeMismatchInSignature _ -> true | _ -> false
  )));

  ("modules/m.mz", simple_test Pass);

  ("modules/qualified.mz", simple_test Pass);

  ("assert.mz", simple_test Pass);

  ("priority.mz", simple_test Pass);

  ("fieldEvaluationOrder.mz", simple_test Pass);

  ("fieldEvaluationOrderReject1.mz", simple_test (Fail (function _ -> true)));

  ("fieldEvaluationOrderReject2.mz", simple_test (Fail (function _ -> true)));

  ("monads.mz", simple_test Pass);

  ("list.mz", simple_test Pass);

  ("mutableTreeMap.mz", simple_test Pass);

  ("adopts-non-mutable-type.mz", simple_test (Fail (function _ -> true)));

  ("adopts-type-variable.mz", simple_test (Fail (function _ -> true)));

  ("ref-confusion.mz", simple_test (Fail (function _ -> true)));

  ("dfs.mz", simple_test Pass);

]

let _ =
  let open Bash in
  Log.enable_debug (-1);
  (* These two are probably a little bit too violent, expect conflicts... *)
  Driver.add_include_dir "tests";
  Driver.add_include_dir "tests/modules";
  let failed = ref 0 in
  List.iter (fun (file, test) ->
    Log.warn_count := 0;
    let do_it = fun () ->
      let env = Driver.process (Filename.concat "tests" file) in
      env
    in
    begin try
      test do_it;
      if !Log.warn_count > 0 then
        Printf.printf "%s✓ %s%s, %s%d%s warning%s\n"
          colors.green colors.default file
          colors.red !Log.warn_count colors.default
          (if !Log.warn_count > 1 then "s" else "")
      else
        Printf.printf "%s✓ %s%s\n" colors.green colors.default file;
    with e ->
      failed := !failed + 1;
      Printf.printf "%s✗ %s%s\n" colors.red colors.default file;
      print_endline (Printexc.to_string e);
      Printexc.print_backtrace stdout;
      if e = Exit then
        raise e
    end;
    flush stdout;
    flush stderr;
  ) tests;
  Printf.printf "%s%d%s tests run, " colors.blue (List.length tests) colors.default;
  if !failed > 0 then
    Printf.printf "%s%d failed, this is BAD!%s\n" colors.red !failed colors.default
  else
    Printf.printf "%sall passed%s, congratulations.\n" colors.green colors.default;
;;
