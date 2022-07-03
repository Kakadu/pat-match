open OCanren
open OCanren.Std
open Tester

let show_intl = GT.show logic (GT.show GT.int)

let run_pair eta =
  run_r
    (Std.Pair.reify OCanren.reify OCanren.reify)
    (GT.show Std.Pair.logic show_intl show_intl)
    eta

let run_list eta =
  run_r (Std.List.reify OCanren.reify) (GT.show Std.List.logic show_intl) eta

let%expect_test ":_" =
  [%tester
    run_pair (-1) (fun q ->
        fresh x
          (q === pair x x)
          (q =/= pair __ !!1)
          (q =/= pair !!1 __)
          trace_diseq_constraints)];
  [%expect {| |}]

(* let ( =//= ) a b = fresh () (a =/= b) *)

let%expect_test ":_" =
  [%tester
    run_pair (-1) (fun q -> fresh () (q =/= __) cut_off_wc_diseq_without_domain)];
  [%expect {| |}]

(*
      let test1 = function
      | _ :: _ -> true
      | _ -> false
*)

let test1o x r =
  (* conde
     [ *)
  (* fresh (h tl) (x === h % tl) (r === !!true); *)
  fresh () (r === !!false)
    (x =/= __ % __)
    trace_diseq_constraints trace_diseq_constraints
(* ] *)

let%expect_test ":_" =
  [%tester run_list (-1) (fun q -> fresh () (test1o q !!false))];
  [%expect {| |}]

let%expect_test ":_" =
  [%tester
    run_list (-1) (fun q ->
        fresh (h tl)
          (q === h % tl)
          (* (q =/= __ % __) *)
          (test1o q !!false)
          trace_diseq_constraints cut_off_wc_diseq_without_domain)];
  [%expect {| |}]
