(** The same as OCanren.tester but with timeing *)

open Printf
open OCanren

(** {3 Helper functions to provide names for top-level variables } *)

let do_print_span = ref true
let set_print_span x =
  (* Printf.printf "%s %b\n%!" __FUNCTION__ x; *)
  do_print_span := x

let print_span span =
  if !do_print_span then
  (let ms = Mtime.Span.to_float_ns span /. 1e6 in
  if ms > 10000.
  then printf "%10.0fs\n%!" (ms /. 1e3)
  else printf "%10.0fms 111 \n%!" ms)

let wrap ~span onOK i (name, x) =
  onOK   i name ~span x

let qh onOK = fun q ~span () ->
  print_span span;
  List.iteri (wrap ~span onOK )   ["q", q]

let qrh onOK  = fun q r ~span () ->
  print_span span;
  List.iteri (wrap ~span onOK )   ["q", q; "r", r]

let qrsh onOK  = fun q r s ~span () ->
  print_span span;
  List.iteri (wrap ~span onOK )   ["q", q; "r", r; "s", s]

let qrsth onOK  = fun q r s t ~span () ->
  print_span span;
  List.iteri (wrap ~span onOK )   ["q", q; "r", r; "s", s; "t", t]

let make_title n msg =
  printf "%s, %s answer%s {\n%!"
    msg
    (if n = (-1) then "all" else string_of_int n)
    (if n <>  1  then "s" else "")

exception NoMoreAnswers

let run_gen ?(do_print_span=true) onFree n num handler (repr, goal) =
  make_title n repr;
  let rec loop st = function
  | k when (k > n) && (n >= 0) -> ()
  | k ->
    let start = Mtime_clock.counter () in
    let stream_rez = Stream.retrieve ~n:1 st in
    let span = Mtime_clock.count start in
    match stream_rez with
    | [],_ ->
        if do_print_span then print_span span;
        raise NoMoreAnswers
    | [f],tl ->
      f ~span ();
      loop tl (k+1)
    | _ -> assert false
  in
  let handler = handler  onFree in
  let () = try loop (run num goal handler) 1 with NoMoreAnswers -> () in
  printf "}\n%!"

let run_r ?(do_print_span=true) reifier printerR =
  run_gen ~do_print_span
    (fun i name ~span (func : _ OCanren.reified) ->
      let ans = func#reify reifier in
      printf "%s%s=%s;\n%!" (if i<>0 then " " else "") name (printerR ~span ans)
      )
