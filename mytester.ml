(** The same as OCanren.tester but with timeing *)

open Printf
open OCanren

(** {3 Helper functions to provide names for top-level variables } *)

let print_span span =
  let ms = Mtime.Span.to_ms span in
  if ms > 10000.0 then printf "%10.0fs \n%!" (Mtime.Span.to_s span)
  else printf "%10.0fms\n%!" ms

let wrap ~span:_ onOK i (name, x) = onOK i name x

let qh onOK q ~span =
  print_span span;
  List.iteri (wrap ~span onOK (* ~span *)) @@ [ ("q", q) ]
(* let qrh onOK q r () = List.iteri (wrap onOK) @@ [ ("q", q); ("r", r) ] *)

(* let qrsh onOK q r s () =
     List.iteri (wrap onOK) @@ [ ("q", q); ("r", r); ("s", s) ]

   let qrsth onOK q r s t () =
     List.iteri (wrap onOK) @@ [ ("q", q); ("r", r); ("s", s); ("t", t) ]
*)
let make_title n msg =
  printf "%s, %s answer%s {\n%!" msg
    (if n = -1 then "all" else string_of_int n)
    (if n <> 1 then "s" else "")

exception NoMoreAnswers

let run_gen onFree n num handler (repr, goal) =
  make_title n repr;
  let rec loop st = function
    | k when k > n && n >= 0 -> ()
    | k -> (
        let start = Mtime_clock.counter () in
        let stream_rez = Stream.retrieve ~n:1 st in
        let span = Mtime_clock.count start in
        match stream_rez with
        | [], _ ->
            print_span span;
            raise NoMoreAnswers
        | [ f ], tl ->
            f ~span;
            printf "\n%!";
            loop tl (k + 1)
        | _ -> assert false)
  in
  let handler = handler onFree in
  let () = try loop (run num goal handler) 1 with NoMoreAnswers -> () in
  printf "}\n%!"

let run_r reifier printerR =
  run_gen (fun i name (func : _ OCanren.reified) ->
      let ans = func#reify reifier in
      printf "%s%s=%s;%!"
        (if i <> 0 then " " else "")
        name
        (printerR ~span:(Obj.magic 1) ans))

let%expect_test _ =
  let open Tester in
  run_r
    (OCanren.prj_exn : (GT.int ilogic, GT.int) Reifier.t)
    (GT.show GT.int) 1 q
    (qh : (int -> string -> GT.int OCanren.reified -> _) -> _)
    ("", fun (q : int ilogic) -> q === !!1)

let%expect_test _ =
  run_r
    (OCanren.prj_exn : (GT.string ilogic, GT.string) Reifier.t)
    (fun ~span : _ -> GT.show GT.string)
    1 q
    (qh : (int -> string -> GT.string OCanren.reified -> _) -> _)
    ("", fun (q : string ilogic) -> q === !!"1");
  [%expect {| 2 |}]
