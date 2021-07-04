open Printf
open OCanren
open Mytester
open Helper
open Unn_pre
open Main_inputs

let () = Mybench.enable ~on:false

type test_t = string * (module Main_inputs.ARG0)

module EnabledTests = struct
  type t = {mutable test: test_t list}

  let use_cygus = ref false
  let is_sygus () = !use_cygus
  let enabled_tests = {test= []}
  let possible_tests = {test= []}
  let addp x = possible_tests.test <- List.append possible_tests.test [x]
  let disable_all () = enabled_tests.test <- []

  let adde ((key, _) as t) =
    let es = List.filter (fun (s, _) -> s <> key) enabled_tests.test in
    enabled_tests.test <- List.append es [t]

  let set_sygus x = use_cygus := x

  let del key =
    enabled_tests.test <-
      List.filter (fun (s, _) -> s <> key) enabled_tests.test
end

let () =
  let t = ("truefalse", (module ArgTrueFalse : Main_inputs.ARG0)) in
  EnabledTests.adde t; EnabledTests.addp t

let () =
  let t = ("pairtruefalse", (module ArgPairTrueFalse : Main_inputs.ARG0)) in
  EnabledTests.addp t

let () =
  let t = ("triplebool", (module ArgTripleBool : Main_inputs.ARG0)) in
  EnabledTests.adde t; EnabledTests.addp t

let () =
  let t = ("simplelist", (module ArgSimpleList : Main_inputs.ARG0)) in
  EnabledTests.addp t

let () =
  let t = ("peano", (module ArgPeanoSimple : Main_inputs.ARG0)) in
  EnabledTests.addp t

let () =
  let t = ("pcf", (module ArgPCF : Main_inputs.ARG0)) in
  EnabledTests.addp t

let () =
  let cmds =
    List.concat_map
      (fun ((name, m) as t) ->
        [ ( "-" ^ name
          , Arg.Unit (fun () -> EnabledTests.adde t)
          , Format.sprintf "Enable the test %s" name )
        ; ( "-no-" ^ name
          , Arg.Unit (fun () -> EnabledTests.del name)
          , Format.sprintf "Disable the test %s" name ) ] )
      EnabledTests.possible_tests.EnabledTests.test
    @ [ ("-bench", Arg.Unit (fun () -> Mybench.enable ~on:true), "")
      ; ("-nothing", Arg.Unit EnabledTests.disable_all, "Disable all tests")
      ; ( "-sygus"
        , Arg.Unit (fun () -> EnabledTests.set_sygus true)
        , "run cvc4 instead of MK" ) ] in
  Arg.parse cmds
    (fun _ -> print_endline "WTF")
    "Running without options start only the tests enabled by default"

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

[%%define AB]
[%%undef AB]
[%%define ABC]
[%%undef ABC]
[%%define TrueFalse]
[%%undef TrueFalse]
[%%define PairTrueFalse]
[%%undef PairTrueFalse]
[%%define TripleBool]

(*[%% undef  TripleBool]*)
[%%define SimpleList]
[%%undef SimpleList]
[%%define Peano]
[%%undef Peano]
[%%define TwoNilLists1]
[%%undef TwoNilLists1]
[%%define TwoNilLists2]
[%%undef TwoNilLists2]
[%%define ABCD]
[%%undef ABCD]
[%%define Tuple5]
[%%undef Tuple5]
[%%define PCF]
[%%undef PCF]

let () =
  (* Format.printf "%d\n%!" (List.length EnabledTests.enabled_tests.test); *)
  EnabledTests.enabled_tests.test
  |> List.iter (fun (name, (module M : ARG0)) ->
         if EnabledTests.is_sygus () then Run_cvc.run (module M : ARG0)
         else
           let (module Algo) = algo in
           let (module Work) = work in
           let module M = Algo.Make (Work) (ArgMake (M)) in
           M.test (-1) )

let () = exit 0
(* ************************************************************************** *)

[%%if defined TrueFalse]

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make (Work) (ArgMake (ArgTrueFalse)) in
  M.test (-1)

[%%endif]

(* ************************************************************************** *)
[%%if defined PairTrueFalse]
(*module FPairBool = Algo_fair.Make(Work)(struct
  include ArgMake(ArgPairTrueFalse)
end)*)

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgPairTrueFalse)) in
  L.test (-1)

[%%endif]

(* ************************************************************************** *)
[%%if defined AB]

module FAAAAAAAAAAAA =
  Algo_fair.Make
    (Work)
    (struct
      include ArgMake (ArgAB)

      (* in this demo merging cases can be helpful *)
    end)

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgAB)) in
  L.test (-1)

[%%endif]

(* ************************************************************************** *)
[%%if defined ABC]
(*module FABC = Algo_fair.Make(Work)(struct
  include ArgMake(ArgABC)

  (* in this demo merging cases can be helpful *)
end)*)

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (ArgMake (ArgABC)) in
  L.test (-1)

[%%endif]

(* ************************************************************************** *)

[%%if defined TripleBool]

module TripleBoolHack1 = struct
  include ArgMake (ArgTripleBool)

  (* we default bound (14) it works very long time *)
  (* let max_ifs_count = 4
     let info = Printf.sprintf "%s + max_ifs_count=%d" info max_ifs_count*)

  (* let ir_hint (rez: IR.injected) =
       let open IR in
       fresh (t a b c d)
         (rez === IR.switch  (Matchable.field1()) Std.((Pair.pair !!(tag_of_string_exn "true") c) % d) b)

     let info = Printf.sprintf "%s + hint" info*)

  (* let shortcut _tag m _branches history rez =
       (rez === !!true) &&& (default_shortcut _tag m _branches history rez)

     let shortcut_tag constr_names cases rez =
       (rez === !!true) &&&
       (default_shortcut_tag constr_names cases rez)*)
end

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module L = Algo.Make (Work) (TripleBoolHack1) in
  (*  let _ = assert false in*)
  L.test (-1)

(*    ~prunes_period:(Some 100)*)
(*    ~prunes_period:None*)
(*    ~check_repeated_ifs:true*)
(*    ~debug_filtered_by_size:true*)

[%%endif]

(*
module TripleBoolHack2 = struct
  include TripleBoolHack1

  let shortcut t _ _ _ rez =
    fresh ()
      (rez === !!true)
      (t =/= Tag.(inject @@ tag_of_string_exn "triple"))

  let info = Printf.sprintf "%s + tag=/=\'triple'" info
end
module FTripleBool2 = Algo_fair.Make(Work)(TripleBoolHack2)

(* first answer -- 34s *)
(*let () = FTripleBool2.test ~prunes_period:None 1*)

(* 18s *)
let __ () =
  FTripleBool2.test
    ~prunes_period:(Some 100)
    (* increasin 100 -> 1000 slightly increases time (probably because later cuts) *)
    ~check_repeated_ifs:true
(*    ~debug_filtered_by_size:true*)
    1


(* ** *)
module TripleBoolHack3 = struct
  include TripleBoolHack1

  let rec nat_lt (x: Nat.injected) y (rez: (bool, _) injected) =
    conde
      [ (y === Nat.z) &&& (rez === !!false)
      ; (x === Nat.z) &&& (y =/= Nat.z) &&& (rez === !!true)
      ; fresh (px py)
          (x === Nat.s px)
          (y === Nat.s py)
          (nat_lt px py rez)
      ]

  (* this can save a couple of seconds *)
  let shortcut_tag constr_names cases rez =
    let open Std in
    conde
      [ fresh ()
          (constr_names === nil ())
(*          (rez === !!false)*)
          failure
      ; fresh (u)
          (constr_names === u % (nil()))
          (cases === nil ())
          (rez === !!true)
      ; fresh (u v w)
          (constr_names === u % (v % w) )
          (rez === !!true)
      ]

  let info = Printf.sprintf "%s + shortcut_tag " info

(*  let () =
    assert
      (OCanren.(run one) (fun q -> (shortcut_tag (Std.Option.some Nat.z) Nat.z !!true) &&& (q === !!true) )
        (fun x -> x)
        |> OCanren.Stream.is_empty
        )*)


  let shortcut t _ _ _ rez =
    fresh ()
      (rez === !!true)
      (t =/= Tag.(inject @@ tag_of_string_exn "triple"))

  let info = Printf.sprintf "%s + tag=/=\'triple' " info
end
module FTripleBool3 = Algo_fair.Make(Work)(TripleBoolHack3)


(* 14 seconds *)
let __ () =
  FTripleBool3.test
    ~prunes_period:(Some 100)
    ~check_repeated_ifs:true
(*    ~debug_filtered_by_size:true*)
    1

module TripleBoolHack4 = struct
  include TripleBoolHack1

(*  let shortcut t m branches rez =
    fresh (h)
      (rez === !!true)
(*      (t =/= Tag.(inject @@ tag_of_string_exn "triple"))*)
      (m =/= Matchable.scru ())
(*      (branches === Std.(!< h))*)*)

(*  let info = Printf.sprintf "%s + tag=/='triple'" info*)
(*  let info = Printf.sprintf "%s + m=/=S" info*)
(*  let info = Printf.sprintf "%s + single_switch_branch" info*)

  let max_ifs_count = 14
(*  let info = Printf.sprintf "%s + max_ifs_count=%d" info max_ifs_count

  let max_nested_switches =
    assert (max_nested_switches = 4);
    3*)
end
module FTripleBool4 = Algo_fair.Make(Work)(TripleBoolHack4)


(* 8 seconds *)
let __ () =
  FTripleBool4.test
(*    ~prunes_period:(Some 100)*)
    ~prunes_period:None
    ~check_repeated_ifs:true
(*    ~debug_filtered_by_size:true*)
    1

module FTripleBool45 = Algo_fair_manual.Make(TripleBoolHack4)
let __ () =
  FTripleBool45.test
    ~prunes_period:(Some 100)
(*    ~prunes_period:None*)
    ~check_repeated_ifs:true
(*    ~debug_filtered_by_size:true*)
    1


(*
(** This we give hint because we know answer. it is very bad *)
module TripleBoolHack4 = struct
  include TripleBoolHack1

  let shortcut t _ cases rez =
    fresh (q)
      (rez === !!true)
      (t =/= Tag.(inject @@ tag_of_string_exn "triple"))
      (cases === Std.List.cons (Std.Pair.pair Tag.(inject @@ tag_of_string_exn "true") q) (Std.nil()))


  let info = Printf.sprintf "%s + tag=/=\'triple'" info
  let info = Printf.sprintf "%s + match_on_true" info
end
module FTripleBool4 = Algo_fair.Make(Work)(TripleBoolHack4)

(* 2s *)
(*(*let () = FTripleBool4.test ~debug_filtered_by_size:false*)
    ~check_repeated_ifs:true
    1*)
*)


module TripleBoolHack41 = struct
  include TripleBoolHack1

  let shortcut t _ cases _ rez =
    fresh (q te)
      (rez === !!true)
      (t =/= Tag.(inject @@ tag_of_string_exn "triple"))
      (cases === Std.List.cons (Std.Pair.pair te q) (Std.nil()))
      (te =/= Tag.(inject @@ tag_of_string_exn "false"))


  let info = Printf.sprintf "%s + tag=/=\'triple'" info
  let info = Printf.sprintf "%s + match_on_not_false" info
end
module FTripleBool41 = Algo_fair.Make(Work)(TripleBoolHack41)


(* 2s *)
(*let () = FTripleBool4.test ~debug_filtered_by_size:false
    ~check_repeated_ifs:true
    1*)

module TripleBoolHack5 = struct
  include TripleBoolHack1

  let shortcut t _ cases _ rez =
    fresh (q te tl)
      (rez === !!true)
      (t =/= Tag.(inject @@ tag_of_string_exn "triple"))
      (cases === Std.List.cons (Std.Pair.pair te q) tl)
(*      (te =/= !!(tag_of_string_exn "false"))*)


  let info = Printf.sprintf "%s + tag=/=\'triple'" info
  let info = Printf.sprintf "%s + match_like_if" info
end

(* ? *)
let __ () =
  let module M = Algo_fair.Make(Work)(TripleBoolHack5) in
(*  M.test ~debug_filtered_by_size:false ~check_repeated_ifs:true 1;*)
  ()
*)

(* ************************************************************************** *)
[%%if defined Peano]

module Peano = struct
  include ArgMake (ArgPeanoSimple)
  (* let shortcut _tag m _branches history rez =
       (rez === !!true) &&& (default_shortcut _tag m _branches history rez)

     let shortcut_tag constr_names cases rez =
       (rez === !!true) &&&
       (default_shortcut_tag constr_names cases rez)*)
end

let () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (Peano) in
  L.test (*    ~debug_filtered_by_size:false*) ~prunes_period:None (-1)

(*[%% if (defined Algo2) ]
let () =
  let module M = Algo_fair2.Make(Peano) in
  M.test (-1) ~prunes_period:None

[%% endif]*)

(*[%% if (defined ManualAlgo) ]
let () =
  let module M = Algo_fair_manual.Make(Peano) in
  M.test (-1) ~prunes_period:None

[%% endif]*)

[%%endif]

(* ************************************************************************** *)

[%%if defined SimpleList]
(*module FairLists1 = Algo_fair.Make(Work)(struct
  include ArgMake(ArgSimpleList)
end)*)

let () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgSimpleList)) in
  L.test (*    ~debug_filtered_by_size:false*) 10

(*[%% if (defined ManualAlgo) ]
let () =
  (* TODO: this call may produce more answers than needed *)
  let module M = Algo_fair_manual.Make(ArgMake(ArgSimpleList)) in
  M.test (10)

[%% endif]*)
[%%endif]

(*
module FairLists2 = Algo_fair.Make(Work)(struct
  include ArgMake(ArgSimpleList)
  (* adding non-pair shourtcut optimizes from 1.8 (for all answers) to 1.4 (for all answers) *)
  let shortcut tag _ _ _ rez =
    fresh ()
      (rez === !!true)      
      (tag =/= Tag.(inject @@ tag_of_string_exn "pair"))

  let info = info ^ " + (=/= pair)"
end)

(*let () = FairLists2.test 10*)


let __ () =
  let module L = Algo_fair.Make(Work)(ArgMake(ArgSimpleList)) in
  L.test (10)


let __ () =
  let module M = Algo_fair_manual.Make(ArgMake(ArgSimpleList)) in
  M.test (-1)
*)

(*module F2NilShort = Algo_fair.Make(Work)(struct
  include ArgMake(ArgTwoNilLists2Cons)
end)*)

(* There are only 4 answers here*)
(*let () = F2NilShort.test (4)*)

[%%if defined TwoNilLists1]

let () =
  let (module Work) = work in
  let module L = Algo_fair.Make (Work) (ArgMake (ArgTwoNilLists2Cons)) in
  L.test 10

(*[%% if (defined ManualAlgo) ]
let () =
  let module M = Algo_fair_manual.Make(ArgMake(ArgTwoNilLists2Cons)) in
  M.test (10)

[%% endif]*)
[%%endif]

(* ************************************************************************** *)
[%%if defined TwoNilLists2]

let () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test 10 ~prunes_period:(Some 100)

let () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test 10 ~prunes_period:(Some 10)

let () =
  let (module Work) = work in
  let (module Algo) = algo in
  let module L = Algo.Make (Work) (ArgMake (ArgTwoNilLists2Simplified)) in
  L.test 10 ~prunes_period:None

(*
[%% if (defined ManualAlgo) ]
let () =
  let module M = Algo_fair_manual.Make(ArgMake(ArgTwoNilLists2Simplified)) in
  M.test (10)
    (*~prunes_period:None*)
    ~prunes_period:(Some 100)
[%% endif]*)

(*module WWW2 = Algo_fair.Make(Work)(struct
  include ArgMake(ArgTwoNilLists2Simplified)

  let info = info ^ "+ max_height=2 + check_repeated_ifs"
end)*)
(*let () = WWW2.test ~check_repeated_ifs:true 10*)

[%%endif]

(* ************************************************************************** *)
(*module XXX = Algo_fair.Make(Work)(struct
  include ArgMake(ArgTwoNilLists2Simplified)
  let shortcut tag _ _ _ rez =
    fresh ()
      (rez === !!true)
      (tag =/= Tag.(inject @@ tag_of_string_exn "pair"))

  let info = info ^ " + tag=/=pair"
end)*)

(*let () = XXX.test 10*)
(*
let __ () =
  let module M = Algo_fair_manual.Make(ArgMake(ArgTwoNilLists2Simplified)) in
  M.test (-1)*)

(* ************************************************************************** *)
(*
module XXX2 = Algo_fair.Make(Work)(struct
  include ArgMake(ArgTwoNilLists2Simplified)
  let shortcut tag _ _ _ rez =
    fresh ()
      (rez === !!true)
      (tag =/= Tag.(inject @@ tag_of_string_exn "pair"))

  let info = info ^ " + tag=/=pair + check_repeated_ifs"

  let ir_hint ir =
    print_endline "applying hint";
    let open Std in
    fresh (c tl def)
      (ir === IR.switch (Matchable.field1 ())
                ((Std.Pair.pair Tag.(inject @@ tag_of_string_exn "cons") c)%tl)
                def)

end)
*)

(* ************************************************************************** *)

[%%if defined ABCD]

let () = Algo_fair_manual.is_enabled := true

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo.Make (Work) (ArgMake (ArgABCD)) in
  M.test (-1)

[%%endif]

(* ************************************************************************** *)
[%%if defined PCF]

let () =
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

[%%endif]

(* ************************************************************************** *)

[%%if defined Tuple5]

let () =
  let (module Algo) = algo in
  let (module Work) = work in
  let module M = Algo_fair.Make (Work) (ArgMake (ArgTuple5)) in
  M.test (-1)

[%%endif]
(* ************************************************************************** *)

let () = Mybench.finish ()
