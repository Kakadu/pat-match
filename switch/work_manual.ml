include (struct
  let well_typed_expr = Unn_pre.WorkUnnesting.well_typed_expr
  let info_assoc = Unn_pre.WorkUnnesting.info_assoc
  let eval_pat = Unn_pre.WorkUnnesting.eval_pat
  let eval_m = Work_unn.eval_m


  let matchable_leq_nat = Unn_pre.WorkUnnesting.matchable_leq_nat

  open OCanren
  open Unn_pre

  let rec not_in_history x xs q29 =
    conde
      [ ((xs === (Std.nil ())) &&& (q29 === (!! true)))
      ; fresh (h tl q32)
          (xs === Std.(h % tl))
          (conde
            [ (x === h) &&& (q32 === (!! true))
            ; (q32 === !!false) &&& (x =/= h)
            ])
          (conde
            [ ((q32 === (!! false)) &&& (not_in_history x tl q29))
            ; ((q32 === (!! true)) &&& (q29 === (!! false)))
            ])
      ]

(*
let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag ir q28 =
  let open Std in
  let rec inner history test_list irrr q0 =
    conde
      [ (irrr === (IR.fail ())) &&& (q0 === (Std.Option.none ()))
      ; fresh (n)
          (irrr === (IR.lit n))
          (q0 === (Option.some n))
      ; fresh (m cases on_default q6 etag args cnames)
          (irrr === (IR.switch m cases on_default))
          (q6 === (pair (Expr.constr etag args) cnames))
          (shortcut0 m max_height cases !! true)
          (eval_m s tinfo m q6)
          (shortcut1 etag m cases history !! true)
          (test_list (m % history) etag cnames on_default cases q0)
      ]
  in
  let rec test_list next_histo etag cnames on_default cases0 q26 =
    let rec helper constr_names cases q9 =
      fresh (q10)
        (conde
          [ (cases === (nil ())) &&& (q10 === (!! true))
          ; (q10 === (!! false)) &&& (cases =/= (nil ()))
          ])
        (conde
          [ ((q10 === (!! true)) &&& (inner next_histo test_list on_default q9))
          ; fresh (constr_hd constr_tl qtag ontag clauses_tl)
              (q10 === (!! false))
              (constr_names === (constr_hd % constr_tl))
              (cases === ((pair qtag ontag) % clauses_tl))

              (* (debug_var constr_names (flip @@ Std.List.reify reify) (fun intl ->
                try
                  let rec helper acc = function
                  | Var _ -> raise Not_found
                  | Value (Std.List.Cons (Var _,_)) -> raise Not_found
                  | Value (Std.List.Cons (Value s, tl)) -> helper (s::acc) tl
                  | Value Nil -> acc
                  in
                  assert (Stdlib.List.length intl = 1);
                  let dom = helper [] (Stdlib.List.hd intl) in
                  FD.domain qtag dom
                with Not_found ->
                  Format.eprintf "SHOLD NOT HAPPEN %s %d\n%!" __FILE__ __LINE__;
                  failure
              )) *)

            (conde
              [ (qtag === constr_hd) &&&
                (conde
                  [ (qtag === etag) &&& (inner next_histo test_list ontag q9)
                  ; (* (FD.neq qtag etag) &&&*) (helper constr_tl clauses_tl q9)
                  (* ; (qtag =/= etag) &&& (helper constr_tl clauses_tl q9) *)
                  ])
              ; (* (FD.neq qtag constr_hd) &&& *) (helper constr_tl cases q9)
              (* ; (qtag =/= constr_hd) &&& (helper constr_tl cases q9) *)
              ])
           ])
    in
    helper cnames cases0 q26 in
  inner (nil ()) test_list ir q28
*)

let (%) = Std.(%)

let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag ir q28 =
  let rec inner history test_list irrr q0 =
    conde
      [ (irrr === (IR.fail ())) &&& (q0 === (Std.none ()))
      ; fresh (n) (irrr === (IR.lit n)) (q0 === (Std.some n))
      ; fresh (m cases on_default q4 q6 etag args cnames q8)
          (irrr === (IR.switch m cases on_default))
          (q4 === (!! true))
          (q6 === (Std.pair (Expr.constr etag args) cnames))
          (q8 === (!! true))
          (shortcut0 m max_height cases q4)
          (eval_m s tinfo m q6)
          (shortcut1 etag m cases history q8)
          (test_list Std.(m % history) etag cnames on_default cases q0)
      ]
    in
  let rec test_list next_histo etag cnames on_default cases0 q26 =
    let rec helper constr_names cases q9 =
      fresh (q10)
        (conde
          [ (cases === (Std.nil ())) &&& (q10 === (!! true))
          ; (q10 === (!! false)) &&& (cases =/= (Std.nil ()))
          ])
        ( ((q10 === (!! true)) &&& (inner next_histo test_list on_default q9)) |||
          (fresh
            (constr_hd constr_tl qtag ontag clauses_tl q14)
            (q10 === (!! false))
            (constr_names === Std.(constr_hd % constr_tl))
            (cases === ((Std.pair qtag ontag) % clauses_tl))
            (conde
              [ (qtag === constr_hd) &&& (q14 === (!! true))
              ; (q14 === (!! false))  &&&(* (* (qtag =/= constr_hd) *) *) (FD.neq qtag constr_hd)
              ])
            (conde
              [ fresh (q16)
                  (q14 === (!! true))
                  (conde
                    [ (qtag === etag) &&& (q16 === (!! true))
                    ; (q16 === (!! false))  &&&(* (* (qtag =/= etag) *) *)(FD.neq qtag etag)
                    ])
                  (conde
                    [ ((q16 === (!! true)) &&& (inner next_histo test_list ontag q9))
                    ; ((q16 === (!! false)) &&& (helper constr_tl clauses_tl q9))
                    ])
              ; (q14 === (!! false)) &&& (helper constr_tl cases q9)
              ]
            )
          )
        )
      in
    helper cnames cases0 q26 in
  inner (Std.nil ()) test_list ir q28


end : Unn_pre.WORK)
