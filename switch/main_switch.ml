open Printf
open OCanren
open Mytester
open Helper
open Unn_pre
open Main_inputs

let () = Mybench.enable ~on:false

let () =
  Arg.parse
    [ ("-bench", Unit (fun () -> Mybench.enable ~on:true), "") ]
    (fun _ -> print_endline "WTF")
    "msg"

let env_work = "PAT_MATCH_WORK"
let env_algo = "PAT_MATCH_ALGO"

let work =
  match Sys.getenv env_work with
  | "unn" -> (module Unn_pre.WorkUnnesting : Unn_pre.WORK)
  | "ho"  -> (module Unn_pre.WorkHO : Unn_pre.WORK)
  | "fd"  -> (module Work_manual : Unn_pre.WORK)
  | _     -> failwith (sprintf "Bad argument of env variable %s" env_work)
  | exception Not_found -> (module Unn_pre.WorkHO : Unn_pre.WORK)

let algo =
  match Sys.getenv env_algo with
  | "manual" -> (module Algo_fair_manual : Main_inputs.ALGO)
  | exception Not_found -> (module Algo_fair : Main_inputs.ALGO)
  | _ -> (module Algo_fair : Main_inputs.ALGO)



[%% define AB]
[%% undef  AB]
[%% define TwoNilLists2]
[%% undef  TwoNilLists2]


[%% define ABC]
[%% undef  ABC]
[%% define TrueFalse]
[%% undef  TrueFalse]
[%% define PairTrueFalse]
[%% undef  PairTrueFalse]
[%% define TripleBool]
(*[%% undef  TripleBool]*)
[%% define SimpleList]
[%% undef  SimpleList]
[%% define Peano]
[%% undef  Peano]
[%% define TwoNilLists1]
[%% undef  TwoNilLists1]

[%% define ABCD]
[%% undef  ABCD]

[%% define Tuple5]
[%% undef  Tuple5]

[%% define PCF]
[%% undef  PCF]
[%% define PCF2]
[%% undef  PCF2]
[%% define PCF3]
[%% undef  PCF3]

(* ************************************************************************** *)

[%% if (defined TrueFalse) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make(Work)(ArgMake(ArgTrueFalse)) in
  M.test (-1)


[%% endif]

(* ************************************************************************** *)
[%% if (defined PairTrueFalse) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make(Work)(ArgMake(ArgPairTrueFalse)) in
  L.test (-1)

[%% endif]

(* ************************************************************************** *)
[%% if (defined AB) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make(Work)(ArgMake(ArgAB)) in
  L.test (-1)

[%% endif]

(* ************************************************************************** *)
[%% if (defined ABC) ]
let  () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make(Work)(ArgMake(ArgABC)) in
  L.test (-1)

[%% endif]

(* ************************************************************************** *)

[%% if (defined TripleBool) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make(Work)(ArgMake(ArgTripleBool)) in
  L.test (-1)
(*    ~prunes_period:(Some 100)*)
(*    ~prunes_period:None*)
(*    ~check_repeated_ifs:true*)
(*    ~debug_filtered_by_size:true*)
[%% endif]



(* ************************************************************************** *)
[%% if (defined Peano) ]
let () =
  let (module Work) = work in
  let module L = Algo_fair.Make(Work)(ArgMake(ArgPeanoSimple)) in

  L.test
(*    ~debug_filtered_by_size:false*)
(*    ~prunes_period:None*)
    (-1)


[%% endif]

(* ************************************************************************** *)

[%% if (defined SimpleList) ]
let () =
  let (module Work) = work in
  let module L = Algo_fair.Make(Work)(ArgMake(ArgSimpleList)) in
  L.test
(*    ~debug_filtered_by_size:false*)
    (10)

[%% endif]

(* ************************************************************************** *)
[%% if (defined TwoNilLists1) ]

let () =
  let (module Work) = work in
  let module L = Algo_fair.Make(Work)(ArgMake(ArgTwoNilLists2Cons)) in
  L.test (10)

(**)
[%% endif]

(* ************************************************************************** *)
[%% if (defined TwoNilLists2) ]

let () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make(Work)(ArgMake(ArgTwoNilLists2Simplified)) in
  L.test 10
    ~prunes_period:(Some 100)


let () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make(Work)(ArgMake(ArgTwoNilLists2Simplified)) in
  L.test 10
    ~prunes_period:(Some 10)


let () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make(Work)(ArgMake(ArgTwoNilLists2Simplified)) in
  L.test 10
    ~prunes_period:None

[%% endif]


(* ************************************************************************** *)

[%% if (defined ABCD) ]

let () = Algo_fair_manual.is_enabled := true

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make(Work)(ArgMake(ArgABCD)) in
  M.test (-1)

[%% endif]

(* ************************************************************************** *)
[%% if (defined PCF) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo_fair.Make(Work)(ArgMake(ArgPCF)) in
  M.test (-1)

[%% endif]

(* ************************************************************************** *)
[%% if (defined PCF2) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo_fair.Make(Work)(struct
    include ArgMake(ArgPCF2)
  end)
  in
(*  M.test (-1)
    ~prunes_period:(Some 777);*)
  M.test (-1)

[%% endif]
(* ************************************************************************** *)
[%% if (defined PCF3) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo_fair.Make(Work)(ArgMake(ArgPCF3))
  in
  M.test (-1)
    ~prunes_period:(Some 100)

[%% endif]

(* ************************************************************************** *)

[%% if (defined Tuple5) ]
let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo_fair.Make(Work)(struct
    include ArgMake(ArgTuple5)
  end)
  in
  M.test (-1)

[%% endif]
(* ************************************************************************** *)

let () =
  Mybench.finish ()
