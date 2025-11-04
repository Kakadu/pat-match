open Printf
open OCanren
open Mytester
open Helper
open Unn_pre
open Main_inputs

let () = Memtrace.trace_if_requested ~context:"my program" ()

type config = { mutable quiet : bool }

let config = { quiet = false }
let env_work = "PAT_MATCH_WORK"

let work =
  match Sys.getenv env_work with
  | "unn" -> (module Unn_pre.WorkUnnesting : Unn_pre.WORK)
  | "ho" -> (module Unn_pre.WorkHO : Unn_pre.WORK)
  | _ -> failwith (sprintf "Bad argument of env variable %s" env_work)
  | exception Not_found -> (module Unn_pre.WorkHO : Unn_pre.WORK)

let algo = (module Algo_fair : Main_inputs.ALGO)
let enabled_tests : (string * (unit -> unit)) list ref = ref []
let all_tests : (string * (unit -> unit)) list ref = ref []

let extend k v =
  assert (List.assoc_opt k !all_tests = None);
  all_tests := (k, v) :: !all_tests

[%%define AB]
[%%undef AB]
[%%define TwoNilLists2]
(* [%%undef TwoNilLists2] *)

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
  M.test Format.std_formatter ~quiet:config.quiet (-1)

let () = extend "true_alse" true_false

[%%endif]

(* ************************************************************************** *)
[%%if defined PairTrueFalse]

let pair_true_false () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgPairTrueFalse)) in
  L.test Format.std_formatter ~quiet:config.quiet (-1)

let () = extend "pair_true_false" pair_true_false

[%%endif]

(* ************************************************************************** *)
[%%if defined AB]

let ab () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgAB)) in
  L.test Format.std_formatter ~quiet:config.quiet (-1)

let () = extend "ab" ab

[%%endif]

(* ************************************************************************** *)
[%%if defined ABC]

let abc () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgABC)) in
  L.test Format.std_formatter ~quiet:config.quiet (-1)

let () = extend "abc" abc

[%%endif]

(* ************************************************************************** *)

[%%if defined TripleBool]

let triple_bool ~prunes_period () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgTripleBool)) in
  L.test Format.std_formatter ~quiet:config.quiet ~prunes_period (-1)

(*    ~prunes_period:(Some 100)*)
(*    ~prunes_period:None*)
(*    ~check_repeated_ifs:true*)
(*    ~debug_filtered_by_size:true*)

let () =
  extend "triple_boolpZ" (triple_bool ~prunes_period:None);
  extend "triple_boolpX" (triple_bool ~prunes_period:(Some 10));
  extend "triple_boolpL" (triple_bool ~prunes_period:(Some 100));
  ()

[%%endif]

(* ************************************************************************** *)
[%%if defined Peano]

let peano () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgPeanoSimple)) in
  L.test Format.std_formatter
    ~quiet:config.quiet (*    ~debug_filtered_by_size:false*)
    ~prunes_period:None (-1)

let () = extend "peano" peano

[%%endif]

(* ************************************************************************** *)

[%%if defined SimpleList]

let simple_list () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgSimpleList)) in
  L.test Format.std_formatter ~quiet:config.quiet
    (*    ~debug_filtered_by_size:false*) 10

let () = extend "simple_list" simple_list

[%%endif]
[%%if defined TwoNilLists1]

let two_nil_lists () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgTwoNilLists2Cons)) in
  L.test ~quiet:config.quiet Format.std_formatter 10

let () = extend "two_nil_lists" two_nil_lists

[%%endif]

(* ************************************************************************** *)
[%%if defined TwoNilLists2]

let two_nil_lists2 ~prunes_period () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test ~quiet:config.quiet Format.std_formatter ~prunes_period 10

let () =
  (* extend "two_nil_lists2pC" (two_nil_lists2 ~prunes_period:(Some 100)); *)
  (* extend "two_nil_lists2pX" (two_nil_lists2 ~prunes_period:(Some 10)); *)
  extend "two_nil_lists2pZ" (two_nil_lists2 ~prunes_period:None)

[%%endif]

(* ************************************************************************** *)

[%%if defined ABCD]

let () = Algo_fair_manual.is_enabled := true

let abcd () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make (Work) (ArgMake (ArgABCD)) in
  M.test ~quiet:config.quiet (-1)

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
  let q = not config.quiet in
  M.test Format.std_formatter ~print_examples:q (-1) ~prunes_period:(Some 777)

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

  let () =
    let single_tests =
      let f (key, f) =
        ( "-" ^ key,
          Arg.Unit
            (fun () ->
              enabled_tests :=
                List.find (fun (s, _) -> s = key) !all_tests :: !enabled_tests;
              f ()),
          Printf.sprintf " Test '%s'" key )
      in
      List.map f !all_tests
    in
    Arg.parse
      ([
         ("-bench", Arg.Unit (fun () -> Mybench.enable ~on:true), "");
         ("-q", Arg.Unit (fun () -> config.quiet <- true), " ");
       ]
      @ single_tests)
      (fun _ -> print_endline "Anonymous arguments not supported")
      "msg"
  in
  if !enabled_tests = [] then enabled_tests := !all_tests;
  List.iter (fun (_, f) -> f ()) !enabled_tests;
  Mybench.finish ()
