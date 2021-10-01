(* A new demo where we configure per example in which parts of scrutinee interpreter should look *)

open Main_inputs
open Unn_pre
open OCanren
open Tester
module W = Unn_pre.WorkHO
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

let run_option_int eta =
  runR
    (Std.Option.reify OCanren.reify)
    (GT.show GT.option @@ GT.show GT.int)
    (GT.show Std.Option.logic @@ GT.show OCanren.logic (GT.show GT.int))
    eta
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
  (* let sl = GT.show OCanren.logic show_int in *)
  runR IR.reify IR.show IR.show_logic eta
;;

let run_pattern eta =
  let show_int = GT.show GT.bool in
  (* let sl = GT.show OCanren.logic show_int in *)
  runR Pattern.reify Pattern.show Pattern.show_logic eta
;;

let default_shortcut0 good_matchables m max_height cases rez =
  let open OCanren in
  fresh
    ()
    (W.matchable_leq_nat m max_height !!true)
    (cases =/= Std.nil ())
    (debug_var m (flip Matchable.reify) (fun ms ->
         (*        Format.printf "default_shortcut0 on matchable %s\n%!" ((GT.show GT.list) Matchable.show_logic ms);*)
         match ms with
         | [] -> failure
         | _ :: _ :: _ -> failwith "too many answers"
         | [ ms ] ->
           (match Matchable.to_ground ms with
           | None -> success
           | Some Matchable.Scru -> failure
           | Some m when List.mem m good_matchables -> rez === MatchableKind.good
           | Some _m ->
             rez === MatchableKind.miss_example
             (* | Some _ -> rez === MatchableKind.good *))))
;;

let default_shortcut _etag m _cases history _rez =
  let open OCanren in
  W.not_in_history m history !!true &&& success
;;

let default_shortcut_tag constr_names cases _rez =
  let open OCanren in
  let open OCanren.Std in
  conde
    [ constr_names === nil () &&& failure
    ; fresh u (constr_names === u % nil ()) (cases === nil ())
    ; fresh (u v w) (constr_names === u % (v % w))
    ]
;;

let __ _ =
  run_pair
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e =/= Std.pair !!true __) (e =/= Std.pair __ !!true)))
;;

module TripleBool = struct
  (*
  match ... with
  | triple (_, false, true) -> 1
  | triple (false, true, _) -> 2
  | triple (_, _, false) -> 3
  | triple (_, _, true) -> 4
  *)

  module GroundField = struct
    open Matchable

    let field0 : ground = Field (N.Z, Scru)
    let field1 : ground = Field (N.(S Z), Scru)
    let field2 : ground = Field (N.(S (S Z)), Scru)
  end

  let examples =
    let open E in
    [ ((fun q -> q === triple __ false_ true_), 1, GroundField.[ field1; field2 ])
    ; ((fun q -> q === triple false_ true_ __), 2, GroundField.[ field0; field1 ])
    ; ((fun q -> q === triple __ __ false_), 3, GroundField.[ field2 ])
    ; ((fun q -> q === triple __ __ true_), 4, GroundField.[ field2 ])
    ]
  ;;

  let answer : IR.injected -> _ =
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

  let _ = [%tester run_ir 1 (fun q -> answer q)]

  let line_num line num =
    fresh
      q
      (debug_var q (flip OCanren.reify) (function _ ->
           Format.printf "%s %d\n%!" line num;
           success))
  ;;

  let _ =
    let desc, _rhs, good_matchables =
      let open E in
      (* (fun q -> q === triple __ false_ true_), 1, GroundField.[ field1; field2 ] *)
      List.nth examples 2
    in
    let desc q =
      let open E in
      fresh () (desc q) (q =/= triple false_ true_ __) (q =/= triple __ false_ true_)
    in
    [%tester run_expr 2 (fun p -> desc p)];
    run_option_int
      2
      q
      qh
      (REPR
         (fun rez ->
           fresh
             (scru tinfo max_height ir)
             (max_height === N.(inject @@ of_int 2))
             (tinfo === Typs.inject Main_inputs.ArgTripleBool.typs)
             (desc scru)
             (answer ir)
             (Work_manual.eval_ir
                scru
                max_height
                tinfo
                (default_shortcut0 good_matchables)
                default_shortcut
                default_shortcut_tag
                ir
                rez)))
  ;;

  let __ _ =
    (* let examples = [ List.nth examples 0; List.nth examples 1; List.nth examples 2 ] in *)
    let examples = List.map (List.nth examples) [ 2 ] in
    run_ir
      3
      q
      qh
      (REPR
         (fun ir ->
           fresh
             (max_height tinfo)
             (max_height === N.inject @@ N.of_int 3)
             (answer ir)
             (List.fold_left
                (fun acc (desc, rhs, good_matchables) ->
                  fresh
                    (scru rez)
                    (rez === Std.Option.some !!rhs)
                    (tinfo === Typs.inject Main_inputs.ArgTripleBool.typs)
                    acc
                    (desc scru)
                    (line_num __FILE__ __LINE__)
                    (Work_manual.eval_ir
                       scru
                       max_height
                       tinfo
                       (default_shortcut0 good_matchables)
                       default_shortcut
                       default_shortcut_tag
                       ir
                       rez))
                success
                examples)))
  ;;

  (* *********************************************************** *)
end
