open Unn_pre

let%expect_test _ =
  let x =
    OCanren.(
      run q (fun (x : IR.injected) ->
          let switch1 a b =
            IR.switch (Matchable.scru ())
              (Std.list (fun (x, y) -> Std.pair (Tag.inject x) y) [])
              b
          in
          x
          === IR.switch (Matchable.scru ())
                (Std.list (fun (x, y) -> Std.pair (Tag.inject x) y) [])
                (switch1 (IR.lit !!2) (IR.lit !!3)))) (fun rr ->
        rr#reify Unn_pre.IR.reify)
    |> OCanren.Stream.hd
  in
  Format.printf "%a%!" IR.fmt_logic x;
  [%expect {|
    (switch S with
     | _ -> (switch S with
             | _ -> 3)) |}]
