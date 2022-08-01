open Lib_ifs
open Synth
open Pre
open OCanren
open OCanren.Std

let%expect_test "example from Maranget 2001" =
  let run_ir eta =
    let open Tester in
    run_r IR.reify (GT.show IR.logic) eta
  in

  let add_domain m ~iftag ~etag:_ ~eargs:_ =
    fresh ()
      (m =/= Matchable.scru ())
      (conde
         [
           iftag === !!(Tag.of_string_exn "true");
           (* e === !!(Tag.of_string_exn "false"); *)
         ])
  in

  let open Tester in
  let branches =
    let open Expr in
    [
      (1, fun s -> s === triple __ false_ true_);
      ( 2,
        fun s ->
          fresh () (s =/= triple __ false_ true_) (s === triple false_ true_ __)
      );
      ( 3,
        fun s ->
          fresh ()
            (s =/= triple __ false_ true_)
            (s =/= triple false_ true_ __)
            (s === triple __ __ false_) );
      ( 4,
        fun s ->
          fresh ()
            (s =/= triple __ false_ true_)
            (s =/= triple false_ true_ __)
            (s =/= triple __ __ false_)
            (s === triple __ __ true_) );
    ]
  in
  let branch_unreachable s =
    let open Expr in
    fresh ()
      (s =/= triple __ false_ true_)
      (s =/= triple false_ true_ __)
      (s =/= triple __ __ false_)
    (* (s =/= triple __ __ true_) *)
  in
  let _ = branch_unreachable in
  [%tester
    run_ir 10 (fun ir ->
        Stdlib.List.fold_left
          (fun acc (rhs, make_scru) ->
            fresh s (make_scru s)
              (eval_ir ~add_domain s tinfo_triple_of_bools ir
                 (Std.Option.some !!rhs))
              acc)
          success branches)];
  [%expect
    {|
    fun ir ->
      Stdlib.List.fold_left
        (fun acc ->
           fun (rhs, make_scru) ->
             fresh s (make_scru s)
               (eval_ir ~add_domain s tinfo_triple_of_bools ir
                  (Std.Option.some (!! rhs))) acc) success branches, 10 answers {
    q=(if S[0] then 4 else (if S[2] then (if S[1] then 2 else 1) else 3));
    q=(if S[0] then 4 else (if S[2] then (if S[1] then 2 else 1) else (if S[1] then 3 else _.1494)));
    q=(if S[0] then 4 else (if S[2] then 1 else (if S[1] then 2 else 3)));
    q=(if S[0] then 4 else (if S[2] then (if S[1] then _.25863 else 1) else (if S[1] then 2 else 3)));
    q=(if S[0] then 4 else (if S[1] then (if S[2] then 2 else 3) else 1));
    q=(if S[0] then 4 else (if S[2] then (if S[1] then 2 else 1) else (if S[1] then _.1493 else 3)));
    q=(if S[0] then 4 else (if S[1] then (if S[2] then 2 else 3) else (if S[2] then 1 else _.35148)));
    q=(if S[0] then 4 else (if S[1] then 2 else (if S[2] then 1 else 3)));
    q=(if S[0] then (if S[1] then 4 else 3) else (if S[1] then 2 else 1));
    q=(if S[0] then (if S[1] then 4 else 3) else (if S[1] then 2 else (if S[2] then 1 else _.99286)));
    } |}];

  [%tester
    run_ir 4 (fun ir ->
        Stdlib.List.fold_left
          (fun acc (rhs, make_scru) ->
            fresh s (make_scru s)
              (eval_ir ~add_domain s tinfo_triple_of_bools ir
                 (Std.Option.some !!rhs))
              acc)
          success
          [ Stdlib.List.hd branches ])];
  [%expect
    {|
    fun ir ->
      Stdlib.List.fold_left
        (fun acc ->
           fun (rhs, make_scru) ->
             fresh s (make_scru s)
               (eval_ir ~add_domain s tinfo_triple_of_bools ir
                  (Std.Option.some (!! rhs))) acc) success
        [Stdlib.List.hd branches], 4 answers {
    q=1;
    q=(if S[0] then 1 else _.17);
    q=(if S[0] then _.16 else 1);
    q=(if S[1] then _.16 else 1);
    } |}];

  let fd_domain_hint m etag eargs =
    conde
      [
        fresh ()
          (m =/= Matchable.scru ())
          (set_boolean_domain etag)
          (eargs === Std.nil ());
        m === Matchable.scru ();
      ]
  in
  let well_formed_scru scru =
    let well_formed_bool b =
      fresh (tag args)
        (b === Expr.constr tag args)
        (args === Std.nil ())
        (set_boolean_domain tag)
    in
    fresh (a b c)
      (scru === Expr.constr !!(Tag.of_string_exn "triple") (a % (b % !<c)))
      (well_formed_bool a) (well_formed_bool b) (well_formed_bool c)
  in
  let trace_scru s1 ~msg =
    debug_var s1 Expr.reify (function xs ->
        Format.printf "%s = %a\n%!" msg [%fmt: Expr.logic GT.list] xs;
        success)
  in
  let _ = well_formed_scru in
  let _ = trace_scru in
  [%tester
    run_ir 1 (fun ir ->
        let open Expr in
        let my_eval sc rhs =
          eval_ir ~add_domain ~fd_domain_hint sc tinfo_triple_of_bools ir
            (Std.Option.option @@ Stdlib.Option.map ( !! ) rhs)
        in

        match branches with
        | [ (rhs1, case1); (rhs2, case2); (rhs3, case3); (rhs4, case4) ] ->
            fresh (s1 s2 s3 s4) (* *)
              (case1 s1) (well_formed_scru s1) (case2 s2) (well_formed_scru s2)
              (case3 s3) (well_formed_scru s3) (case4 s4) (well_formed_scru s4)
              (* ******************* ********************* ********* *)
              (my_eval s1 (Some rhs1))
              (my_eval s2 (Some rhs2)) (my_eval s3 (Some rhs3))
              (my_eval s4 (Some rhs4))
            (* *** *** *** *** *** *** *** *** *** *)
            (* (fresh slast (branch_unreachable slast)
               (trace_scru slast ~msg:"slast")) *)
            (* (trace_scru s1 ~msg:"s1")
               (trace_scru s2 ~msg:"s2") (trace_scru s3 ~msg:"s3")
               (trace_scru s4 ~msg:"s4") *)
            (* *** *** *** *** *** *** *** *** *** *)
            (* trace_diseq_constraints trace_domain_constraints *)
        | _ -> assert false)];
  [%expect
    {xxx|
    fun ir ->
      let open Expr in
        let my_eval sc rhs =
          eval_ir ~add_domain ~fd_domain_hint sc tinfo_triple_of_bools ir
            (Std.Option.option @@ (Stdlib.Option.map (!!) rhs)) in
        match branches with
        | (rhs1, case1)::(rhs2, case2)::(rhs3, case3)::(rhs4, case4)::[] ->
            fresh (s1 s2 s3 s4) (case1 s1) (well_formed_scru s1) (case2 s2)
              (well_formed_scru s2) (case3 s3) (well_formed_scru s3) (case4 s4)
              (well_formed_scru s4) (my_eval s1 (Some rhs1))
              (my_eval s2 (Some rhs2)) (my_eval s3 (Some rhs3))
              (my_eval s4 (Some rhs4))
        | _ -> assert false, 1 answer {
    q=(if S[1] then (if S[0] then (if S[2] then 4 else 3) else 2) else 1);
    } |xxx}]
