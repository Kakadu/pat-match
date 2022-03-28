open OCanren
open Tester

let _ =
  let open Work_matchable_kind in
  let open Std in
  let goal q =
    fresh (a b a2 b2 a3 b3 ir)
      (q === Std.pair a b % (Std.pair a2 b2 % (Std.pair a3 b3 % Std.nil ())))
      (dirty_hack q (Std.some !!1) ir ~f:(fun _ rhs rez ->
           conde [ rhs === rez; rhs === rez ]))
  in
  runR
    (Std.List.reify (Std.Pair.reify OCanren.reify OCanren.reify))
    ([%show: (GT.string, GT.int) Std.Pair.ground Std.List.ground] ())
    ([%show:
       (GT.string OCanren.logic, GT.int OCanren.logic) Std.Pair.logic
       Std.List.logic] ())
    1 q qh ("", goal)
