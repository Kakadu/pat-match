open Main_inputs
open Unn_pre
open OCanren
open Tester
module W = Work_matchable_kind
module Arg = Main_inputs.ArgMake (Main_inputs.ArgPairTrueFalse)

module E = struct
  open OCanren.Std

  let pair a b = Expr.constr !!(Tag.inttag_of_string_exn "pair") (a %< b)

  let triple a b c =
    Expr.constr !!(Tag.inttag_of_string_exn "triple") (a % (b %< c))

  let true_ = Expr.constr !!(Tag.inttag_of_string_exn "true") (nil ())
  let false_ = Expr.constr !!(Tag.inttag_of_string_exn "false") (nil ())
end

let run_int eta =
  run_r OCanren.reify (GT.show OCanren.logic @@ GT.show GT.int) eta

let run_bool eta =
  run_r OCanren.reify (GT.show OCanren.logic @@ GT.show GT.bool) eta

let run_pair eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  run_r
    (Std.Pair.reify OCanren.reify OCanren.reify)
    (GT.show Std.Pair.logic sl sl)
    eta

let run_ir eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  run_r IR.reify IR.show_logic eta

let run_expr eta = run_r Expr.reify Expr.show_logic eta

let __ _ =
  let () = () in
  (* [%tester run_bool (-1) (fun q -> q =/= !!true &&& (q =/= !!false))]; *)
  run_bool (-1) q qh (REPR (fun q -> q =/= !!true &&& (q =/= !!false)));
  exit 1

let default_shortcut0 good_matchables m max_height cases rez =
  let open OCanren in
  fresh ()
    (W.matchable_leq_nat m max_height !!true)
    (cases =/= Std.nil ())
    (debug "inside default_shortcut0")
    (debug_var m Matchable.reify (fun ms ->
         let set = Matchable.Set.of_list ms in
         if Matchable.Set.is_empty set then failure
         else
           let ms = Matchable.Set.min_elt set in
           (* match Stdlib.List. ms with
              | [] -> failure
              | _ :: _ :: _ ->
                  Format.printf "default_shortcut0 on matchable %s\n%!"
                    ((GT.show GT.list) Matchable.show_logic ms);
                  failwith "too many answers" *)
           match Matchable.to_ground ms with
           | None ->
               Format.printf "non-ground matchable is %a\n%!"
                 (GT.fmt Matchable.logic) ms;
               success
           | Some Matchable.Scru -> failure
           | Some m when List.mem m good_matchables ->
               rez === MatchableKind.good
           | Some _m -> rez === MatchableKind.miss_example))

let default_shortcut _etag m _cases history _typs _rez =
  let open OCanren in
  W.not_in_history m history !!true &&& success

let default_shortcut_tag etag constr_names rez =
  let open OCanren in
  let open OCanren.Std in
  fresh () (rez === !!true)
    (debug_var constr_names (Std.List.reify OCanren.reify) (function
      | [ lst ] -> (
          try
            let ground_list =
              Std.List.from_logic
                (function Value x -> x | _ -> raise OCanren.Not_a_value)
                lst
            in

            fresh () (OCanren.FD.domain etag ground_list)
          with OCanren.Not_a_value ->
            Format.eprintf "Not_a_value when reifying type names. Skip\n%!";
            success)
      | _ -> assert false))

let default_shortcut4 (t1 : Tag.injected) t2 rez =
  fresh flag
    (debug_var (Std.triple t1 t2 rez)
       (Std.Triple.reify Tag.reify Tag.reify OCanren.reify) (function
      | [ Value (t1, t2, Var (n, _)) ] ->
          let __ _ =
            Format.printf "default_shortcut4 of (%s, %s, _.%d)\n%!"
              (Tag.show_logic t1) (Tag.show_logic t2) n
          in
          success
      | _ -> assert false))
    (OCanren.unif_hack t1 t2 flag)
    (conde
       [
         flag =/= !!true &&& (rez === !!true);
         flag =/= !!false &&& (rez === !!false);
       ])

let __ _ =
  let printed_clauses =
    Format.printf "%a\n%!" Clauses.pretty_print Arg.clauses
  in
  let injected_clauses = Clauses.inject Arg.clauses in
  run_r IR.reify IR.show_logic (-1) q qh
    (REPR
       (fun ans ->
         let open OCanren.Std in
         fresh scru
           (scru
           === Expr.constr
                 !!(Tag.inttag_of_string_exn "pair")
                 (E.false_ %< E.true_))
           (W.eval_pat scru injected_clauses (Std.Option.some ans))));
  ()

(* *********************************************************** *)
module GroundField = struct
  open Matchable

  let scru = Scru
  let field0 : ground = Field (N.Z, Scru)
  let field1 : ground = Field (N.(S Z), Scru)
  let field2 : ground = Field (N.(S (S Z)), Scru)
end

let _0 : IR.injected = IR.int !!0
let _1 : IR.injected = IR.int !!1
let _2 : IR.injected = IR.int !!2
let _3 : IR.injected = IR.int !!3

module PairsDirtyHack = struct
  (*
  match ... with
  | pair (true, _) -> 0
  | pair (_, true) -> 1
  | pair (_, _) -> 2

  q=(switch S[0] with
    | true -> 0
    | _ -> (switch S[1] with
              | true -> 1
              | _ -> 2 )

  *)

  let program : IR.injected -> _ =
   fun q ->
    let open OCanren.Std in
    let field0 = Matchable.field0 () in
    let field1 = Matchable.field1 () in
    let ite cond c th el = IR.switch cond !<(Std.pair c th) el in
    let ttrue = !!(Tag.of_string_exn "true") in
    let tfalse = !!(Tag.of_string_exn "false") in
    (* fresh () (q === ite field0 ttrue (ite field1 ttrue _0 _1) (ite field1 tfalse _2 _3)) *)
    fresh () (q === ite field0 ttrue _0 (ite field1 ttrue _1 _2))

  let examples =
    let open E in
    [
      (0, (fun q -> fresh () (q === pair true_ __)), GroundField.[ field0 ]);
      ( 1,
        (fun q -> fresh () (q =/= pair true_ __) (q === pair __ true_)),
        GroundField.[ field1 ] );
      ( 2,
        (fun q ->
          fresh (ta tb)
            (q =/= pair true_ __)
            (q =/= pair __ true_)
            (q === pair (Expr.leaf ta) (Expr.leaf tb))
            (FD.domain ta
               [ Tag.of_string_exn "true"; Tag.of_string_exn "false" ])
            (FD.domain tb
               [ Tag.of_string_exn "true"; Tag.of_string_exn "false" ])
            (* (ta =/= !!(Tag.of_string_exn "true")) *)
            (* (tb =/= !!(Tag.of_string_exn "true")) *)
            success),
        GroundField.[] );
    ]

  let eval_ir_pairs ~fields scru ir rez =
    fresh max_height
      (max_height === N.(inject @@ of_int 2))
      (Work_matchable_kind.eval_ir scru max_height
         (Typs.inject ArgPairTrueFalse.typs)
         (default_shortcut0 fields) default_shortcut default_shortcut_tag
         default_shortcut4 ir rez)

  let test_example ~fields n make_scru =
    run_int 3 q qh
      ( Format.sprintf "===== Running forward example %d in TripleBool test" n,
        fun rhs ->
          fresh (scru ir rez)
            (rez === Std.Option.some rhs)
            (program ir) (make_scru scru)
            (eval_ir_pairs ~fields scru ir rez)
            (debug_var scru Expr.reify (function xs ->
                 List.iteri
                   (fun n q ->
                     Format.printf "\t%d: %s\n%!" n (Expr.show_logic q))
                   xs;
                 success)) )

  let __ _ =
    let _, x, fields = List.nth examples 0 in
    test_example ~fields 0 x

  let __ _ =
    let _, x, fields = List.nth examples 1 in
    test_example ~fields 1 x

  let __ _ =
    let _, x, fields = List.nth examples 2 in
    test_example ~fields 2 x

  let __ _ =
    run_ir 1 q qh
      (REPR
         (fun ir ->
           List.fold_left
             (fun acc (rhs, desc, fields) ->
               fresh (scru rez)
                 (rez === Std.Option.some !!rhs)
                 acc (desc scru)
                 (eval_ir_pairs ~fields scru ir rez))
             success
             [ List.nth examples 0; List.nth examples 1; List.nth examples 2 ]))
end

module PairsVerySimple = struct
  (*
  match ... with
  | pair (true, _) -> 0
  | pair (_, true) -> 1
  | pair (_, _) -> 2


  q=(switch S[0] with
    | true -> 0
    | _ -> (switch s[1] with true -> 1 | _ -> 2 )

  *)

  (* let program : IR.injected -> _ =
     fun q ->
      let open OCanren.Std in
      let field0 = Matchable.field0 () in
      let field1 = Matchable.field1 () in
      let ite cond c th el = IR.switch cond !<(Std.pair c th) el in
      let ttrue = !!(Tag.of_string_exn "true") in
      let tfalse = !!(Tag.of_string_exn "false") in
      fresh () (q === ite field0 ttrue _0 _1) *)

  let examples =
    let open E in
    [
      (0, (fun q -> fresh () (q === pair true_ __)), GroundField.[ field0 ]);
      (1, (fun q -> fresh _25 (q =/= pair __ true_)), GroundField.[ field1 ]);
      (2, (fun q -> fresh _25 (q =/= pair __ __)), GroundField.[]);
    ]

  let eval_ir_pairs ~fields scru ir rez =
    fresh max_height
      (max_height === N.(inject @@ of_int 2))
      (Work_matchable_kind.eval_ir scru max_height
         (Typs.inject ArgPairTrueFalse.typs)
         (default_shortcut0 fields) default_shortcut default_shortcut_tag
         default_shortcut4 ir rez)

  (* let test_example ~fields n init_scru =
     run_int 3 q qh
       ( Format.sprintf "===== Running forward example %d in PairVerySimple test"
           n,
         fun rhs ->
           fresh (scru ir rez)
             (rez === Std.Option.some rhs)
             (program ir) (init_scru scru)
             (eval_ir_pairs ~fields scru ir rez)
             (debug_var scru Expr.reify (function xs ->
                  List.iteri
                    (fun n q ->
                      Format.printf "\t%d: %s\n%!" n (Expr.show_logic q))
                    xs;
                  success)) )
  *)
  (* let __ _ =
       let _, x, fields = List.nth examples 0 in
       test_example ~fields 0 x

     let __ _ =
       let _, x, fields = List.nth examples 1 in
       test_example ~fields 1 x *)

  let _ =
    run_ir 1 q qh
      (REPR
         (fun ir ->
           fresh m
             (ir === IR.switch m __ __)
             (ir
             === IR.switch m Std.(!<(pair !!(Tag.of_string_exn "true") __)) __)
             (List.fold_left
                (fun acc (rhs, init_scru, fields) ->
                  fresh (scru rez) acc
                    (* (Work_matchable_kind.debug_ir "inside fold" ir) *)
                    (debug_lino __FILE__ __LINE__)
                    (rez === Std.Option.some !!rhs)
                    (init_scru scru)
                    (eval_ir_pairs ~fields scru ir rez)
                    (Work_matchable_kind.debug_expr "exampful scru = " scru)
                    trace_diseq_constraints cut_off_wc_diseq_without_domain
                    success)
                success
                [
                  List.nth examples 0;
                  List.nth examples 1 (* List.nth examples 2; *);
                ])))
end

(*

cutting off sub_scru: (pair [(false []); (false []); _.1510 [=/= ]])
*)
