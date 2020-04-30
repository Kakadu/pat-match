open GT

open OCanren
open OCanren.Std
open Mytester

open GCW

(*************************************************)

let show_person = function
  | G -> "G"
  | W -> "W"
  | C -> "C"
  | N -> "N"

let myshow x = show List.ground show_person x
let reifier env x = Std.List.reify OCanren.reify env x

(*************************************************)

(** For high order conversion **)
(*let checkAnswer q r = checkAnswer ((===) q) r*)

(** For call-by-need conversion **)
(* let checkAnswer q r = (snd checkAnswer) ([Obj.magic q], (===) q) r *)


let simple_query q = checkAnswer q !!true

let _ =
  run_exn myshow (2) q qh ("simple", fun q ->
    simple_query q
  )


let hackery q =

  let rec lo_length acc = function
  | Var (_,_) -> acc
  | Value (Std.List.Cons (_, tl)) -> lo_length (1+acc) tl
  | Value Nil -> acc
  in

  let cond (wtf: person logic Std.List.logic) =
    let fail = false in
    let ok = true in

    let lo_len = lo_length 0 wtf in
    if lo_len > 9 then fail
    else ok
  in

  (structural q reifier cond) &&& (simple_query q)

let _ =
  run_exn myshow (22) q qh ("with structural", fun q ->
    hackery q
  )
