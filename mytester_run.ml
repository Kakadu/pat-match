open Mytester
open OCanren

let () =
  run_r
    (OCanren.prj_exn : (GT.string ilogic, GT.string) Reifier.t)
    (fun ~span ->
      Mytester.print_span span;
      GT.show GT.string)
    1 q
    (qh : (int -> string -> GT.string OCanren.reified -> _) -> _)
    ("", fun (q : string ilogic) -> q === !!"1")
