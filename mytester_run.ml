open Mytester
open OCanren
open OCanren.Std

let () =
  run_r
    (OCanren.prj_exn : (GT.int ilogic, GT.int) Reifier.t)
    (fun ~span:_ ->
      (* Mytester.print_span span; *)
      GT.show GT.int)
    1 q qh
    ( "",
      fun (q : int ilogic) ->
        fresh (xs tl)
          (xs === q % tl)
          (List.reverso xs (Std.list ( !! ) (Stdlib.List.init 100 Fun.id))) )
