open GT

open OCanren
open OCanren.Std
open Mytester

open Lorry

(*************************************************)

let show_number num =
  let rec helper = function
  | O   -> 0
  | S x -> 1  + (helper x)
  in
  string_of_int @@ helper num

let show_step = function
  | Left x  -> Printf.sprintf "L%s" @@ show_number x
  | Right x -> Printf.sprintf "R%s" @@ show_number x
  | Fill    -> "F"
  | Pour x  -> Printf.sprintf "P%s" @@ show_number x

let myshow x = show List.ground show_step x

(*************************************************)

let rec of_int i = if i = 0 then o () else s @@ of_int @@ i - 1

let rec nat_reifier env x = For_gnat.reify nat_reifier env x
let step_reifier env x = For_gstep.reify nat_reifier env x
let reifier env x = Std.List.reify  step_reifier env x

(** For high order conversion **)
(*let checkAnswer a q p r = checkAnswer ((===) a) ((===) q) ((===) p) r*)

(** For call-by-need conversion **)
(* let checkAnswer q a b r = (snd checkAnswer) ([Obj.magic q], (===) q) ([], (===) a) ([], (===) b) r *)

let ffff () =
  run_exn myshow (1) q qh ("no structural ", fun q ->
    checkAnswer q (of_int 7) (of_int 5) (some @@ of_int 13)
  )

let hack maxlen q a b c =
  let fail = false in
  let ok = true in

  let rec lo_length acc = function
  | Var (_,_) -> acc
  | Value (Std.List.Cons (_, tl)) -> lo_length (1+acc) tl
  | Value Nil -> acc
  in

  let cond wtf =
    let lo_len = lo_length 0 wtf in
    if lo_len > maxlen then fail
    else ok
  in
  (structural q reifier cond) &&& (checkAnswer q a b c)

let _f () =
  run_exn myshow (1) q qh ("with structural", fun q ->
    hack 13 q (of_int 7) (of_int 5) (some @@ of_int 13)  (* 6 seconds *)
  )



let () =
  Helper.show_local_time ();
(*  let start = Mtime_clock.counter () in*)
  for i=1 to 13 do
    let msg = Printf.sprintf "with structural (maxlength = %d)" i in
    run_exn myshow (1) q qh (msg, fun q ->
      hack i q (of_int 7) (of_int 5) (some @@ of_int 13)  (* 6 seconds *)
    )
  done;
(*  let span = Mtime_clock.count start in*)
(*  print_span span;*)
  Helper.show_local_time ();
  ()
