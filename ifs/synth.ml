open OCanren
open OCanren.Std
open Pre

let rec list_assoc : _ -> _ Std.List.injected -> _ -> goal =
 fun name ys q203 ->
  fresh (k v xs q205)
    (ys === pair k v % xs)
    (conde
       [ k === name &&& (q205 === !!true); q205 === !!false &&& (k =/= name) ])
    (conde
       [
         q205 === !!true &&& (v === q203);
         q205 === !!false &&& list_assoc name xs q203;
       ])

let info_assoc :
    Typ_info.injected ->
    Tag.injected ->
    Typ_info.injected Std.List.injected ->
    goal =
 fun tt name q82 ->
  fresh xs (Pre.Typ_info.unwrap tt xs) (list_assoc name xs q82)

let rec list_nth_nat : N.injected -> 'el Std.List.injected -> 'el -> goal =
 fun idx xs rez ->
  fresh q134
    (q134 === pair idx xs)
    (conde
       [
         fresh (x q135) (q134 === pair Pre.N.z (x % q135)) (x === rez);
         fresh (n q137 xs)
           (q134 === pair (N.s n) (q137 % xs))
           (list_nth_nat n xs rez);
       ])

let rec eval_m :
    Expr.injected ->
    Typ_info.injected ->
    Matchable.injected ->
    sub_expr:Expr.injected ->
    sub_typ_info:Typ_info.injected ->
    goal =
 fun s typinfo0 path0 ~sub_expr ~sub_typ_info ->
  let rec helper path current_expr (current_typinfo : Typ_info.injected) =
    conde
      [
        fresh ()
          (path === Matchable.scru ())
          (sub_expr === current_expr)
          (sub_typ_info === typinfo0);
        fresh
          (nth subpath constr_tag es sub_expr args_tinfo_list sub_typ_info temp)
          (path === Matchable.field nth subpath)
          (Typ_info.unwrap sub_typ_info temp)
          (current_expr === Expr.eConstr constr_tag es)
          (list_nth_nat nth es sub_expr)
          (info_assoc current_typinfo constr_tag args_tinfo_list)
          (list_nth_nat nth args_tinfo_list sub_typ_info)
          (helper subpath sub_expr sub_typ_info);
      ]
  in
  fresh () (helper path0 s typinfo0)

let rec not_in_history q xs =
  conde
    [
      xs === Std.nil ();
      fresh (h tl) (xs === h % tl) (h =/= q) (not_in_history q tl);
    ]

let extend_history new_m his new_his = new_his === new_m % his

let rec eval_ir ?(add_domain = fun _ _ -> success) s tinfo :
    IR.injected -> _ Std.Option.groundi -> goal =
  let rec inner history irrr rez =
    conde
      [
        fresh n (irrr === IR.lit n) (rez === Std.Option.some n);
        fresh () (irrr === IR.fail ()) (rez === Std.Option.none ());
        fresh
          (tag m br_th br_el new_history sub_expr sub_typ_info etag)
          (irrr === IR.ite m tag br_th br_el)
          (* (m =/= Matchable.scru ()) *)
          (add_domain m tag)
          (not_in_history m history)
          (extend_history m history new_history)
          (eval_m s tinfo m ~sub_expr ~sub_typ_info)
          (sub_expr === Expr.eConstr etag __)
          (conde
             [
               etag === tag &&& inner new_history br_th rez;
               etag =/= tag &&& inner new_history br_el rez;
             ]);
      ]
  in

  fun ir rez -> inner (Std.nil ()) ir rez

let run_ir eta =
  let open Tester in
  run_r IR.reify (GT.show IR.logic) eta

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
  let add_domain m _ = m =/= Matchable.scru () in
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
    q=(if S[0] = _.105 [=/= true] then 2 else 1);
    q=(if S[0] = _.105 [=/= true] then 2 else 1);
    } |}]

let tinfo_triple_of_bools =
  let bool =
    Typ_info.mkt
      [
        (Tag.of_string_exn "true", Std.List.of_list Fun.id []);
        (Tag.of_string_exn "false", Std.List.of_list Fun.id []);
      ]
  in
  Typ_info.mkt
    [
      (Tag.of_string_exn "triple", Std.List.of_list Fun.id [ bool; bool; bool ]);
    ]
  |> Typ_info.inject

let%expect_test "example from Maranget 2001" =
  let run_ir eta =
    let open Tester in
    run_r IR.reify (GT.show IR.logic) eta
  in

  let add_domain m e =
    fresh ()
      (m =/= Matchable.scru ())
      (conde
         [
           e === !!(Tag.of_string_exn "true");
           e === !!(Tag.of_string_exn "false");
         ])
  in

  let open Tester in
  (* [%tester
       run_ir 1 (fun ir ->
           fresh ()
             (fresh s
                (s === Expr.pair Expr.true_ __)
                (eval_ir s tinfo_pair_of_bools ir (Std.Option.some !!1))))];
     [%expect
       {|
       fun ir ->
         fresh ()
           (fresh s (s === (Expr.pair Expr.true_ __))
              (eval_ir s tinfo_pair_of_bools ir (Std.Option.some (!! 1)))), 1 answer {
       q=(Int 1) ;
       } |}]; *)
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
  [%tester
    run_ir 4 (fun ir ->
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
                  (Std.Option.some (!! rhs))) acc) success branches, 4 answers {
    q=(if S[0] = true then 4 else (if S[2] = true then (if S[1] = true then 2 else 1) else 3));
    q=(if S[0] = true then 4 else (if S[2] = true then (if S[1] = true then 2 else 1) else 3));
    q=(if S[0] = true then 4 else (if S[2] = true then (if S[1] = true then 2 else 1) else 3));
    q=(if S[0] = true then 4 else (if S[2] = true then (if S[1] = false then 1 else 2) else 3));
    } |}]

let%expect_test "match ... with _,F,T -> 1 | F,T,_ -> 2 | _ -> 3" =
  let add_domain m e =
    fresh ()
      (m =/= Matchable.scru ())
      (conde
         [
           e === !!(Tag.of_string_exn "true");
           e === !!(Tag.of_string_exn "false");
         ])
  in

  let open Tester in
  let branches =
    let open Expr in
    [
      (1, fun s -> s === triple __ false_ true_);
      (* ( 2,
           fun s ->
             fresh () (s =/= triple __ false_ true_) (s === triple false_ true_ __)
         ); *)
      ( 3,
        fun s ->
          fresh ()
            (s =/= triple __ false_ true_)
            (* (s =/= triple false_ true_ __) *)
            (s === triple __ __ __) );
    ]
  in
  [%tester
    run_ir 4 (fun ir ->
        match branches with
        | [ (rhs1, case1); (rhs2, case2) ] ->
            fresh ()
              (fresh s (case1 s)
                 (eval_ir ~add_domain s tinfo_triple_of_bools ir
                    (Std.Option.some !!rhs1)))
              (fresh s (case2 s)
                 (eval_ir ~add_domain s tinfo_triple_of_bools ir
                    (Std.Option.some !!rhs2)))
        | _ -> assert false)];
  [%expect
    {|
    fun ir ->
      match branches with
      | (rhs1, case1)::(rhs2, case2)::[] ->
          fresh ()
            (fresh s (case1 s)
               (eval_ir ~add_domain s tinfo_triple_of_bools ir
                  (Std.Option.some (!! rhs1))))
            (fresh s (case2 s)
               (eval_ir ~add_domain s tinfo_triple_of_bools ir
                  (Std.Option.some (!! rhs2))))
      | _ -> assert false, 4 answers {
    q=(if S[0] = true then 1 else 3);
    q=(if S[0] = true then 1 else 3);
    q=(if S[0] = true then 3 else 1);
    q=(if S[0] = true then 3 else 1);
    } |}];

  let dummy_ir =
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
  [%expect {|
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
  [%expect {|
    fun rhs ->
      let (_, make_scru) = Stdlib.List.nth branches 1 in
      fresh scru (make_scru scru)
        (eval_ir ~add_domain scru tinfo_triple_of_bools dummy_ir rhs), all answers {
    q=Some (1);
    q=Some (3);
    q=Some (1);
    q=Some (3);
    } |}];
  ()
