open Lib_ifs
open Synth
open Pre
open OCanren
open OCanren.Std

let run_int_option eta =
  let open Tester in
  run_r
    (Std.Option.reify OCanren.reify)
    ([%show: GT.int logic Std.Option.logic] ())
    eta

let%expect_test "match ... with (T,_) -> 1 | (_,_) -> 2" =
  let tinfo_pair_of_bools =
    let bool =
      Typ_info.mkt
        [
          (Tag.of_string_exn "true", Std.List.of_list Fun.id []);
          (Tag.of_string_exn "false", Std.List.of_list Fun.id []);
        ]
    in

    Typ_info.mkt
      [ (Tag.of_string_exn "pair", Std.List.of_list Fun.id [ bool; bool ]) ]
    |> Typ_info.inject
  in
  let add_domain m ~iftag:_ ~etag:_ ~eargs:_ = m =/= Matchable.scru () in
  let open Tester in
  [%tester
    run_ir 1 (fun ir ->
        fresh ()
          (fresh s
             (s === Expr.pair Expr.true_ __)
             (eval_ir ~add_domain s tinfo_pair_of_bools ir (Std.Option.some !!1))))];
  [%expect
    {|
    fun ir ->
      fresh ()
        (fresh s (s === (Expr.pair Expr.true_ __))
           (eval_ir ~add_domain s tinfo_pair_of_bools ir (Std.Option.some (!! 1)))), 1 answer {
    q=1;
    } |}];
  let branches =
    [
      (1, fun s -> s === Expr.pair Expr.true_ __);
      (2, fun s -> s =/= Expr.pair Expr.true_ __);
    ]
  in
  [%tester
    run_ir 2 (fun ir ->
        Stdlib.List.fold_left
          (fun acc (rhs, make_scru) ->
            fresh s (make_scru s)
              (eval_ir ~add_domain s tinfo_pair_of_bools ir
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
               (eval_ir ~add_domain s tinfo_pair_of_bools ir
                  (Std.Option.some (!! rhs))) acc) success branches, 2 answers {
    q=(if S[0] = _.106 [=/= true] then 2 else 1);
    q=(if S[0] then 1 else 2);
    } |}]
