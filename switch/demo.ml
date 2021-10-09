open Main_inputs
open Unn_pre
open OCanren
open Tester
module W = Work_manual
module Arg = Main_inputs.ArgMake (Main_inputs.ArgPairTrueFalse)

module E = struct
  open OCanren.Std

  let pair a b = Expr.constr !!(Tag.inttag_of_string_exn "pair") (a %< b)
  let triple a b c = Expr.constr !!(Tag.inttag_of_string_exn "triple") (a % (b %< c))
  let true_ = Expr.constr !!(Tag.inttag_of_string_exn "true") (nil ())
  let false_ = Expr.constr !!(Tag.inttag_of_string_exn "false") (nil ())
end

let run_int eta =
  runR OCanren.reify (GT.show GT.int) (GT.show OCanren.logic @@ GT.show GT.int) eta
;;

let run_bool eta =
  runR OCanren.reify (GT.show GT.bool) (GT.show OCanren.logic @@ GT.show GT.bool) eta
;;

let run_expr eta = runR Expr.reify Expr.show Expr.show_logic eta

let __ _ =
  let () = () in
  (* [%tester run_bool (-1) (fun q -> q =/= !!true &&& (q =/= !!false))]; *)
  run_bool (-1) q qh (REPR (fun q -> q =/= !!true &&& (q =/= !!false)));
  exit 1
;;

let default_shortcut0 m max_height cases rez =
  let open OCanren in
  fresh
    ()
    (debug_var m (flip Matchable.reify) (fun ms ->
         (*        Format.printf "default_shortcut0 on matchable %s\n%!" ((GT.show GT.list) Matchable.show_logic ms);*)
         match ms with
         | [] -> failure
         | _ :: _ :: _ -> failwith "too many answers"
         | [ ms ] ->
           (match Matchable.to_ground ms with
           | None -> success
           | Some Matchable.Scru -> failure
           | Some _m -> success)))
    (W.matchable_leq_nat m max_height !!true)
    (cases =/= Std.nil ())
    (rez === !!true)
;;

let default_shortcut _etag m _cases history _typs _rez =
  let open OCanren in
  W.not_in_history m history !!true &&& success
;;

let default_shortcut_tag etag constr_names rez =
  let open OCanren in
  let open OCanren.Std in
  fresh
    ()
    (rez === !!true)
    (debug_var
       constr_names
       (flip @@ Std.List.reify OCanren.reify)
       (function
         | [ lst ] ->
           (try
              let ground_list =
                Std.List.prj_exn
                  (function
                    | Value x -> x
                    | _ -> raise OCanren.Not_a_value)
                  lst
                |> Std.List.to_list Fun.id
              in
              OCanren.FD.domain etag ground_list
            with
           | OCanren.Not_a_value ->
             Format.eprintf "Not_a_value when reifying type names. Skip\n%!";
             success)
         | _ -> assert false))
;;

let __ _ =
  let printed_clauses = Format.printf "%a\n%!" Clauses.pretty_print Arg.clauses in
  let injected_clauses = Clauses.inject Arg.clauses in
  runR
    IR.reify
    IR.show
    IR.show_logic
    (-1)
    q
    qh
    (REPR
       (fun ans ->
         let open OCanren.Std in
         fresh
           scru
           (scru === Expr.constr !!(Tag.inttag_of_string_exn "pair") (E.false_ %< E.true_))
           (W.eval_pat scru injected_clauses (Std.Option.some ans))));
  ()
;;

let __ _ =
  run_expr
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e =/= E.pair E.true_ __) (e =/= E.pair __ E.true_)))
;;

let __ _ =
  run_expr
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e === E.(pair __ true_)) (e =/= E.(pair true_ __))))
;;

let run_pair eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  runR
    (Std.Pair.reify OCanren.reify OCanren.reify)
    (GT.show Std.Pair.ground show_int show_int)
    (GT.show Std.Pair.logic sl sl)
    eta
;;

let run_ir eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  runR IR.reify IR.show IR.show_logic eta
;;

let __ _ =
  run_pair
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e =/= Std.pair !!true __) (e =/= Std.pair __ !!true)))
;;

(*

match ... with
| pair (_, true) -> 1
| pair (true, _) -> 1
| pair (false, false) -> 0

*)
let __ _ =
  let examples =
    [ (* (fun q -> q === E.(pair true_ __)), 1
    ; (fun q -> fresh () (q === E.(pair __ true_)) (q =/= E.(pair true_ __))), 2
    ; *)
      (fun q -> q === E.(pair __ true_)), 1
    ; (fun q -> fresh () (q === E.(pair true_ __)) (q =/= E.(pair __ true_))), 2
    ; ( (fun q ->
          fresh
            ()
            (q === E.(pair false_ false_))
            (q =/= E.(pair true_ __))
            (q =/= E.(pair __ true_)))
      , 3 )
    ]
  in
  let exampels = List.rev examples in
  let eval_ir scru ir rez =
    fresh
      (max_height tinfo)
      (max_height === N.(inject @@ of_int 2))
      (W.eval_ir
         scru
         max_height
         tinfo
         default_shortcut0
         default_shortcut
         default_shortcut_tag
         ir
         rez)
  in
  run_ir
    2
    q
    qh
    ( "IR"
    , fun ir ->
        fresh
          ()
          (List.fold_left
             (fun acc (desc, rhs) ->
               fresh
                 (scru rez)
                 (rez === Std.Option.some !!rhs)
                 acc
                 (desc scru)
                 (eval_ir scru ir rez))
             success
             examples) )
;;

let __ _ =
  let make_program (q : IR.injected) =
    let open Matchable in
    let open IR in
    let open Std in
    fresh
      (v1 bs b1 b2)
      (q === switch (field0 ()) bs (int !!3))
      (b1 === Std.pair v1 (int !!1))
      (v1 === !!(Tag.of_string_exn "true"))
      (v1 === !!(Tag.of_string_exn "false"))
      (b2 === Std.pair (Tag.inject (Tag.of_string_exn "true")) (int !!2))
      (bs === b1 %< b2)
    (* (bs === !<b1) *)
  in
  (* let make_scru q = q === E.(pair true_ true_) in *)
  let make_scru q = q === E.(pair __ true_) in
  let eval_ir scru ir rez =
    fresh
      (max_height tinfo)
      (max_height === N.(inject @@ of_int 2))
      (make_program ir)
      (make_scru scru)
      (W.eval_ir
         scru
         max_height
         tinfo
         default_shortcut0
         default_shortcut
         default_shortcut_tag
         ir
         rez)
  in
  run_int
    2
    q
    qh
    ( "???"
    , fun rhs ->
        fresh
          (scru ir rez)
          (rez === Std.Option.some rhs)
          (make_program ir)
          (eval_ir scru ir rez) );
  exit 1
;;

(*

match ... with
| triple (_, false, true) -> 1
| triple (false, true, _) -> 2
| triple (_, _, false) -> 3
| triple (_, _, true) -> 4

*)
let __ _ =
  let examples =
    let open E in
    [ (fun q -> q === triple __ false_ true_), 1
    ; (fun q -> fresh () (q === triple false_ true_ __) (q =/= triple __ false_ true_)), 2
    ; ( (fun q ->
          fresh
            ()
            (q === triple __ __ false_)
            (q =/= triple false_ true_ __)
            (q =/= triple __ false_ true_))
      , 3 )
    ; ( (fun q ->
          fresh
            ()
            (q === triple __ __ true_)
            (q =/= triple __ __ false_)
            (q =/= triple false_ true_ __)
            (q =/= triple __ false_ true_))
      , 4 )
    ]
  in
  run_ir
    3
    q
    qh
    (REPR
       (fun ir ->
         fresh
           (max_height tinfo)
           (max_height === N.(inject @@ of_int 2))
           (List.fold_left
              (fun acc (desc, rhs) ->
                fresh
                  (scru rez)
                  (rez === Std.Option.some !!rhs)
                  (tinfo === Typs.inject Main_inputs.ArgTripleBool.typs)
                  acc
                  (desc scru)
                  (W.eval_ir
                     scru
                     max_height
                     tinfo
                     default_shortcut0
                     default_shortcut
                     default_shortcut_tag
                     ir
                     rez))
              success
              examples)))
;;

(* *********************************************************** *)

(*
match ... with
| triple (_, false, true) -> 1
| triple (false, true, _) -> 2
| triple (_, _, false) -> 3
| triple (_, _, true) -> 4

1st branch is going to have exponentional examples,
other branches will be describe by =/= with wildcards
*)
let __ _ =
  let examples =
    let open E in
    [ (fun q -> q === triple true_ false_ true_), 1
    ; (fun q -> q === triple false_ false_ true_), 1 (* Wildcards go below *)
    ; (fun q -> fresh () (q =/= triple __ false_ true_)), 2
    ; ( (fun q ->
          fresh
            ()
            (* (q === triple __ __ false_) *)
            (q =/= triple false_ true_ __)
            (q =/= triple __ false_ true_))
      , 3 )
    ; ( (fun q ->
          fresh
            ()
            (* (q === triple __ __ true_) *)
            (q =/= triple __ __ false_)
            (q =/= triple false_ true_ __)
            (q =/= triple __ false_ true_))
      , 4 )
    ]
  in
  let eval_ir scru ir rez =
    fresh
      (max_height tinfo)
      (max_height === N.(inject @@ of_int 2))
      (tinfo === Typs.inject Main_inputs.ArgTripleBool.typs)
      (W.eval_ir
         scru
         max_height
         tinfo
         default_shortcut0
         default_shortcut
         default_shortcut_tag
         ir
         rez)
  in
  run_ir
    3
    q
    qh
    (REPR
       (fun ir ->
         fresh
           ()
           (List.fold_left
              (fun acc (desc, rhs) ->
                fresh
                  (scru rez)
                  (rez === Std.Option.some !!rhs)
                  acc
                  (desc scru)
                  (eval_ir scru ir rez))
              success
              examples)))
;;

(* *********************************************************** *)

(*
match ... with
| pair (true, _) -> 1
| pair (false, _) -> 2
*)
let __ _ =
  let examples =
    let open E in
    [ (fun q -> q === pair true_ __), 1; (fun q -> q === pair false_ __), 2 ]
  in
  let eval_ir scru ir rez =
    fresh
      (max_height tinfo)
      (max_height === N.(inject @@ of_int 2))
      (tinfo === Typs.inject Main_inputs.ArgPairTrueFalse.typs)
      (W.eval_ir
         scru
         max_height
         tinfo
         default_shortcut0
         default_shortcut
         default_shortcut_tag
         ir
         rez)
  in
  run_ir
    10
    q
    qh
    (REPR
       (fun ir ->
         fresh
           ()
           (List.fold_left
              (fun acc (desc, rhs) ->
                fresh
                  (scru rez)
                  (rez === Std.Option.some !!rhs)
                  acc
                  (desc scru)
                  (eval_ir scru ir rez))
              success
              examples)))
;;

let __ _ =
  let make_program (q : IR.injected) =
    let open Matchable in
    let open IR in
    let open Std in
    fresh
      (v1 bs b1)
      (q === switch (field1 ()) bs (int !!2))
      (b1 === Std.pair v1 (int !!1))
      (v1 === !!(Tag.of_string_exn "true"))
      (bs === !<b1)
  in
  (* let make_scru q = q === E.(pair true_ true_) in *)
  let make_scru q = q === E.(pair false_ __) in
  let eval_ir scru ir rez =
    fresh
      (max_height tinfo)
      (max_height === N.(inject @@ of_int 2))
      (make_program ir)
      (make_scru scru)
      (W.eval_ir
         scru
         max_height
         tinfo
         default_shortcut0
         default_shortcut
         default_shortcut_tag
         ir
         rez)
  in
  let injected_clauses =
    let ppair l r =
      Pattern.PConstr (Tag.of_string_exn "pair", Std.List.of_list Fun.id [ l; r ])
    in
    let ptrue = Pattern.PConstr (Tag.of_string_exn "true", Std.List.Nil) in
    let pfalse = Pattern.PConstr (Tag.of_string_exn "false", Std.List.Nil) in
    Clauses.inject
    @@ [ ppair ptrue Pattern.WildCard, IR.Lit 1; ppair pfalse Pattern.WildCard, IR.Lit 2 ]
  in
  let run_interpreter_1 scru rhs =
    W.eval_pat scru injected_clauses (Std.Option.some rhs)
  in
  [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.false_ E.false_) q)];
  [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.false_ E.true_) q)];
  [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.true_ E.false_) q)];
  [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.true_ E.true_) q)];
  [%tester run_ir 2 (fun q -> fresh w (run_interpreter_1 (E.pair E.false_ w) q))];
  run_int
    2
    q
    qh
    ( "???"
    , fun rhs ->
        fresh
          (scru ir rez)
          (rez === Std.Option.some rhs)
          (make_program ir)
          (eval_ir scru ir rez) );
  exit 1
;;

(*

conde
  [ (q === pair true  __) &&& (res=/=1) &&& failure
  ; (q === pair true  __) &&& (res===1)
  ; (q === pair __ false) &&& (res=/=2) &&& failure
  ; (q === pair __ false) &&& (res===2)
  ;
  ]
*)

module _ = struct
  (*
  match ... with
  | triple (_, false, true) -> 1
  | triple (false, true, _) -> 2
  | triple (_, _, false) -> 3
  | triple (_, _, true) -> 4
  *)

  let program : IR.injected -> _ =
   fun q ->
    let open OCanren.Std in
    let field0 = Matchable.field0 () in
    let field1 = Matchable.field1 () in
    let field2 = Matchable.field2 () in
    let ite cond c th el = IR.switch cond !<(Std.pair c th) el in
    let ttrue = !!(Tag.of_string_exn "true") in
    let _1 = IR.int !!1 in
    let _2 = IR.int !!2 in
    let _3 = IR.int !!3 in
    let _4 = IR.int !!4 in
    fresh
      ()
      (q
      === ite
            field1
            ttrue
            (ite field0 ttrue (ite field2 ttrue _4 _3) _2)
            (ite field2 ttrue _1 _3))
 ;;

  let examples =
    let add_domain q =
      FD.domain q [ Tag.of_string_exn "true"; Tag.of_string_exn "false" ]
    in
    let open E in
    [ (fun q -> fresh () (q === triple __ false_ true_)), 1
    ; (fun q -> fresh () (q =/= triple __ false_ true_) (q === triple false_ true_ __)), 2
    ; ( (fun q ->
          fresh
            ()
            (q =/= triple __ false_ true_)
            (q =/= triple false_ true_ __)
            (q === triple __ __ false_))
      , 3 )
    ; ( (fun q ->
          fresh
            ()
            (q =/= triple __ false_ true_)
            (q =/= triple false_ true_ __)
            (q =/= triple __ __ false_)
            (q === triple __ __ true_))
      , 4 )
    ]
  ;;

  let eval_ir_triple_bool scru ir rez =
    fresh
      max_height
      (max_height === N.(inject @@ of_int 2))
      (Work_manual.eval_ir
         scru
         max_height
         (Typs.inject ArgTripleBool.typs)
         default_shortcut0
         default_shortcut
         default_shortcut_tag
         ir
         rez)
  ;;

  let test_example n =
    let make_scru q = fst (List.nth examples n) q in
    (* let run_interpreter_1 scru rhs =
      W.eval_pat scru injected_clauses (Std.Option.some rhs)
    in *)
    (* [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.false_ E.false_) q)];
    [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.false_ E.true_) q)];
    [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.true_ E.false_) q)];
    [%tester run_ir 2 (fun q -> run_interpreter_1 (E.pair E.true_ E.true_) q)];
    [%tester run_ir 2 (fun q -> fresh w (run_interpreter_1 (E.pair E.false_ w) q))]; *)
    run_int
      2
      q
      qh
      ( Format.sprintf "Running forward %dnd example in TripleBool test" n
      , fun rhs ->
          fresh
            (scru ir rez)
            (rez === Std.Option.some rhs)
            (program ir)
            (make_scru scru)
            (eval_ir_triple_bool scru ir rez)
            (debug_var scru (flip Expr.reify) (function xs ->
                 List.iteri
                   (fun n q -> Format.printf "\t%d: %s\n%!" n (Expr.show_logic q))
                   xs;
                 success)) )
  ;;

  (* let _ = test_example 2 *)
  let _ = test_example 3

  let _ =
    run_ir
      3
      q
      qh
      (REPR
         (fun ir ->
           List.fold_left
             (fun acc (desc, rhs) ->
               fresh
                 (scru rez)
                 (rez === Std.Option.some !!rhs)
                 acc
                 (desc scru)
                 (eval_ir_triple_bool scru ir rez))
             success
             [ List.nth examples 0
             ; List.nth examples 1
             ; List.nth examples 2
             ; List.nth examples 3
             ]))
  ;;
end
