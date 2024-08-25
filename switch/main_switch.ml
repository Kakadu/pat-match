open Printf
open OCanren
open Mytester
open Helper
open Unn_pre
open Main_inputs

let env_work = "PAT_MATCH_WORK"

let work =
  match Sys.getenv env_work with
  | "unn" -> (module Unn_pre.WorkUnnesting : Unn_pre.WORK)
  | "ho" -> (module Unn_pre.WorkHO : Unn_pre.WORK)
  | _ -> failwith (sprintf "Bad argument of env variable %s" env_work)
  | exception Not_found -> (module Unn_pre.WorkHO : Unn_pre.WORK)

let algo =
  match Sys.getenv "PAT_MATCH_ALGO" with
  | "manual" -> (module Algo_fair_manual : Main_inputs.ALGO)
  | exception Not_found -> (module Algo_fair : Main_inputs.ALGO)
  | _ -> (module Algo_fair : Main_inputs.ALGO)

let enabled_tests : (string * (unit -> unit)) list ref = ref []

let extend k v =
  assert (List.assoc_opt k !enabled_tests = None);
  enabled_tests := (k, v) :: !enabled_tests

[%%define AB]
[%%undef AB]
[%%define TwoNilLists2]
[%%undef TwoNilLists2]
[%%define ABC]

(*[%% undef  ABC]*)
[%%define TrueFalse]

(*[%% undef  TrueFalse]*)
[%%define PairTrueFalse]

(*[%% undef  PairTrueFalse]*)
[%%define TripleBool]

(*[%% undef  TripleBool]*)
[%%define SimpleList]

(*[%% undef  SimpleList]*)
[%%define Peano]

(*[%% undef  Peano]*)
[%%define TwoNilLists1]
(*[%% undef  TwoNilLists1]*)

[%%define ABCD]
[%%undef ABCD]
[%%define Tuple5]
[%%undef Tuple5]
[%%define PCF]
(*[%% undef  PCF]*)

(* ************************************************************************** *)

[%%if defined TrueFalse]

let true_false () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make (Work) (ArgMake (ArgTrueFalse)) in
  M.test (-1)

let () = extend "true_alse" true_false

[%%endif]

(* ************************************************************************** *)
[%%if defined PairTrueFalse]

let pair_true_false () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgPairTrueFalse)) in
  L.test (-1)

let () = extend "pair_true_false" pair_true_false

[%%endif]

(* ************************************************************************** *)
[%%if defined AB]

let ab () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgAB)) in
  L.test (-1)

let () = extend "ab" ab

[%%endif]

(* ************************************************************************** *)
[%%if defined ABC]

let abc () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgABC)) in
  L.test (-1)

let () = extend "abc" abc

[%%endif]

(* ************************************************************************** *)

[%%if defined TripleBool]

let triple_bool () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgTripleBool)) in
  L.test (-1)

(*    ~prunes_period:(Some 100)*)
(*    ~prunes_period:None*)
(*    ~check_repeated_ifs:true*)
(*    ~debug_filtered_by_size:true*)

let () = extend "triple_bool" triple_bool

[%%endif]

(* ************************************************************************** *)
[%%if defined Peano]

let peano () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgPeanoSimple)) in
  L.test (*    ~debug_filtered_by_size:false*) ~prunes_period:None (-1)

let () = extend "peano" peano

[%%endif]

(* ************************************************************************** *)

[%%if defined SimpleList]

let simple_list () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgSimpleList)) in
  L.test (*    ~debug_filtered_by_size:false*) 10

let () = extend "simple_list" simple_list

[%%endif]
[%%if defined TwoNilLists1]

let two_nil_lists () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgTwoNilLists2Cons)) in
  L.test 10

let () = extend "two_nil_lists" two_nil_lists

[%%endif]

(* ************************************************************************** *)
[%%if defined TwoNilLists2]

let two_nil_lists2_I () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test 10 ~prunes_period:(Some 100)

let two_nil_lists2_II () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test 10 ~prunes_period:(Some 10)

let two_nil_lists2_III () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test 10 ~prunes_period:None

let two_nil_lists2 () =
  two_nil_lists2_I ();
  two_nil_lists2_II ();
  two_nil_lists2_III ();
  ()

let () = extend "two_nil_lists2" two_nil_lists2

[%%endif]

(* ************************************************************************** *)

[%%if defined ABCD]

let () = Algo_fair_manual.is_enabled := true

let abcd () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make (Work) (ArgMake (ArgABCD)) in
  M.test (-1)

let () = extend "abcd" abcd

[%%endif]

(* ************************************************************************** *)
[%%if defined PCF]

let pcf () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M =
    Algo_fair.Make
      (Work)
      (struct
        include ArgMake (ArgPCF)

        let max_examples_count = 10
      end)
  in
  M.test (-1) ~prunes_period:(Some 777)

let () = extend "pcf" pcf

[%%endif]

(* ************************************************************************** *)

[%%if defined Tuple5]

let tuple5 () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M =
    Algo_fair.Make
      (Work)
      (struct
        include ArgMake (ArgTuple5)
      end)
  in
  M.test (-1)

[%%endif]
(* ************************************************************************** *)

let () =
  let () = Mybench.enable ~on:false in
  let run_all_tests = ref true in
  let () =
    let single_tests =
      ListLabels.map !enabled_tests ~f:(fun (key, f) ->
          ( "-" ^ key,
            Arg.Unit
              (fun () ->
                run_all_tests := false;
                f ()),
            Printf.sprintf " Test '%s'" key ))
    in
    Arg.parse
      ([ ("-bench", Arg.Unit (fun () -> Mybench.enable ~on:true), "") ]
      @ single_tests)
      (fun _ -> print_endline "anonymous arguments not supported")
      "msg"
  in
  if !run_all_tests then List.iter (fun (_, f) -> f ()) !enabled_tests;
  Mybench.finish ()
