open Lib_ifs
open Synth
open Pre
open OCanren
open OCanren.Std

let%expect_test "match ... with _,F,T -> 1 | F,T,_ -> 2 | _ -> 3" =
  (*
  if s[1] then
    if s[0] then 3
    else 2
  else
    if s[2] then 1
    else 3

  *)
  let add_domain m ~iftag ~etag:_ ~eargs:_ =
    fresh ()
      (m =/= Matchable.scru ())
      (conde
         [
           (* allowing only true here avoids IR with `if false ...` *)
           iftag === !!(Tag.of_string_exn "true");
           (* e === !!(Tag.of_string_exn "false"); *)
         ])
  in
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
  let open Tester in
  let branches =
    let open Expr in
    [
      (* (1, fun s -> s === triple __ false_ true_); *)
      (1, fun s -> s === triple true_ false_ true_);
      (1, fun s -> s === triple false_ false_ true_);
      ( 2,
        fun s ->
          fresh ()
            (s =/= triple __ false_ true_)
            (s === triple false_ true_ false_)
            success );
      ( 2,
        fun s ->
          fresh ()
            (s =/= triple __ false_ true_)
            (s === triple false_ true_ true_)
            success );
      ( 3,
        fun s ->
          fresh ()
            (s =/= triple __ false_ true_)
            (s =/= triple false_ true_ __)
            (s === triple __ __ __) );
    ]
    |> Stdlib.List.rev
  in
  let branch_unreachable s =
    let open Expr in
    fresh ()
      (s =/= triple __ false_ true_)
      (s =/= triple false_ true_ __)
      (s =/= triple __ __ __)
    (* (s === pair __ __) *)
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
  let my_eval ir sc rhs =
    eval_ir ~add_domain ~fd_domain_hint sc tinfo_triple_of_bools ir
      (Std.Option.option @@ Stdlib.Option.map ( !! ) rhs)
  in
  let smart_iterator ir lst =
    let rec loop i acc cases =
      match cases with
      | [] ->
          Stdlib.List.fold_left
            (fun acc (n, v) ->
              trace_scru v ~msg:(Printf.sprintf "s%d" n) &&& acc)
            success acc
      | (rhs, make_scru) :: tl ->
          Fresh.one (fun s ->
              make_scru s &&& well_formed_scru s &&& my_eval ir s (Some rhs)
              &&& loop (i + 1) ((i, s) :: acc) tl)
    in
    loop 1 [] lst
  in
  [%tester
    run_ir 2 (fun ir ->
        smart_iterator ir branches
        (*
        match branches with
        | [ (rhs1, case1); (rhs2, case2); (rhs3, case3) ] ->
            fresh (s1 s2 s3)
              (* (ir
                 === IR.ite (Matchable.field1 ()) __
                       (IR.ite (Matchable.field0 ()) __ __ __)
                       (IR.ite (Matchable.field2 ()) __ __ __)) *)
              (ir
              === IR.ite (Matchable.field0 ()) __
                    (IR.ite (Matchable.field0 ()) __ __ __)
                    __)
              (case1 s1) (case2 s2) (case3 s3) (well_formed_scru s1)
              (well_formed_scru s2) (well_formed_scru s3)
              (* *** *** *** *** *)
              (my_eval ir s1 (Some rhs1))
              (my_eval ir s2 (Some rhs2))
              (* (my_eval s3 (Some rhs3)) *)
              (* (fresh other (branch_unreachable other)
                 (* *** *** *** *** *** *** *** *** *)
                 (my_eval other (Some 42))) *)
              (* (my_eval s3 (Some rhs3)) *)
              (* *** *)
              (trace_scru s1 ~msg:"s1")
              (trace_scru s2 ~msg:"s2")
        (* (trace_scru s3 ~msg:"s3") *)
        (* *** *)
        | _ -> assert false
        *))];
  [%expect
    {|
    fun ir -> smart_iterator ir branches, 2 answers {
    s1 = [ (triple [(true []); (true []); (_.22 [])])]
    s2 = [ (triple [(false []); (true []); (true [])])]
    s3 = [ (triple [(false []); (true []); (false [])])]
    s4 = [ (triple [(false []); (false []); (true [])])]
    s5 = [ (triple [(true []); (false []); (true [])])]
    q=(if S[0] then (if S[1] then 3 else 1) else (if S[1] then 2 else 1));
    s1 = [ (triple [(true []); (true []); (_.22 [])])]
    s2 = [ (triple [(false []); (true []); (true [])])]
    s3 = [ (triple [(false []); (true []); (false [])])]
    s4 = [ (triple [(false []); (false []); (true [])])]
    s5 = [ (triple [(true []); (false []); (true [])])]
    q=(if S[0] then (if S[1] then 3 else (if S[2] then 1 else _.12624)) else (if S[1] then 2 else 1));
    } |}];

  (* let dummy_ir =
       IR.ITE
         ( Matchable.(Field (N.Z, Scru)),
           Tag.of_string_exn "true",
           IR.Lit 1,
           IR.Lit 3 )
       |> IR.inject
     in
     [%tester
       run_int_option (-1) (fun rhs ->
           let _, make_scru = Stdlib.List.nth branches 0 in
           fresh scru (make_scru scru)
             (eval_ir ~add_domain scru tinfo_triple_of_bools dummy_ir rhs))];
     [%expect
       {|
       fun rhs ->
         let (_, make_scru) = Stdlib.List.nth branches 0 in
         fresh scru (make_scru scru)
           (eval_ir ~add_domain scru tinfo_triple_of_bools dummy_ir rhs), all answers {
       q=Some (1);
       q=Some (3);
       } |}];
     [%tester
       run_int_option (-1) (fun rhs ->
           let _, make_scru = Stdlib.List.nth branches 1 in
           fresh scru (make_scru scru)
             (eval_ir ~add_domain scru tinfo_triple_of_bools dummy_ir rhs))];
     [%expect
       {|
       fun rhs ->
         let (_, make_scru) = Stdlib.List.nth branches 1 in
         fresh scru (make_scru scru)
           (eval_ir ~add_domain scru tinfo_triple_of_bools dummy_ir rhs), all answers {
       q=Some (1);
       q=Some (3);
       } |}]; *)
  ()
