open Main_inputs
open Unn_pre
open OCanren
open Tester
module W = Unn_pre.WorkHO
module Arg = Main_inputs.ArgMake (Main_inputs.ArgPairTrueFalse)

module E = struct
  open OCanren.Std

  let pair a b = Expr.constr !!(Tag.inttag_of_string_exn "pair") (a %< b)
  let true_ = Expr.constr !!(Tag.inttag_of_string_exn "true") (nil ())
  let false_ = Expr.constr !!(Tag.inttag_of_string_exn "false") (nil ())
end

let __ _ =
  let printed_clauses =
    Format.printf "%a\n%!" Clauses.pretty_print Arg.clauses in
  let injected_clauses = Clauses.inject Arg.clauses in
  runR IR.reify IR.show IR.show_logic (-1) q qh
    (REPR
       (fun ans ->
         let open OCanren.Std in
         fresh scru
           ( scru
           === Expr.constr
                 !!(Tag.inttag_of_string_exn "pair")
                 (E.false_ %< E.true_) )
           (W.eval_pat scru injected_clauses (Std.Option.some ans)) ) );
  ()

let _ =
  runR Expr.reify Expr.show Expr.show_logic (-1) q qh
    (REPR (fun e -> fresh () (e =/= E.pair E.true_ __) (e =/= E.pair __ E.true_))
    )

let run_pair eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  runR
    (Std.Pair.reify OCanren.reify OCanren.reify)
    (GT.show Std.Pair.ground show_int show_int)
    (GT.show Std.Pair.logic sl sl)
    eta

let _ =
  run_pair (-1) q qh
    (REPR
       (fun e -> fresh () (e =/= Std.pair !!true __) (e =/= Std.pair __ !!true))
    )
