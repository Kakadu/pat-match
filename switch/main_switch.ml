open Printf
open Work
open OCanren
open Mytester
open Helper
open Unn_pre



let eleaf s = eConstr !!(tag_of_string_exn s) @@ Std.List.nil ()
let epair a b = eConstr !!(tag_of_string_exn "pair") @@ Std.List.list [a;b]

let print_demos msg xs =
  Printf.printf "<%s>\n" msg;
  List.iter (fun p -> Printf.printf "\t\t%s\n" (Expr.show p)) xs;
  Printf.printf "</%s>\n" msg




module EvalMRez = struct
  type ground = (Expr.ground, tag Std.List.ground) Std.Pair.ground
(*      [@@deriving gt ~options: { show; fmt }]*)
  type logic = (Expr.logic, tag OCanren.logic Std.List.logic) Std.Pair.logic
(*      [@@deriving gt ~options: { show; fmt }]*)
  type injected = (ground, logic) OCanren.injected

  let show x = GT.(show Std.Pair.ground Expr.show (show Std.List.ground @@ show GT.string)) x
  let show_logic x = GT.(show Std.Pair.logic Expr.show_logic (show Std.List.logic (show OCanren.logic @@ show GT.string))) x

  let reifier env x = Std.Pair.reify Expr.reify (Std.List.reify OCanren.reify) env x
end


let eval_ir :
  Expr.injected -> Nat.injected -> Typs.injected ->
  _ ->
  IR.injected  ->
  (int, int OCanren.logic) Std.Option.groundi -> goal =
    Work.eval_ir

let eval_m : Expr.injected ->  Typs.injected -> Matchable.injected ->
  EvalMRez.injected ->
  goal
  = Work.eval_m
(*
let _f ()  =
  run_exn (GT.show Std.Option.ground @@ GT.show GT.int) 1 q qh ("test eval_ir", fun q ->
    eval_ir
      (epair (eleaf "aaa") (eleaf "bbb"))
      (Nat.inject @@ Nat.of_int 2)
      Typs.(inject @@ construct @@ T [ ("pair", [ T [ ("aaa", []) ]; T [ ("bbb", []) ] ]) ])
      simple_shortcut
      (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
      q
  )

let _foo () =
  runR Expr.reify Expr.show Expr.show_logic
        1 q qh ("answers", fun q ->
     eval_ir
        q
        (Nat.inject @@ Nat.of_int 2)
        Typs.(inject @@ construct @@ T [ ("pair", [ T [ ("aab", []) ]; T [ ("bbb", []) ] ]) ])
        simple_shortcut
        (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))        
        (Std.some (!!2))
  )

let _f () =
  let e1 = Expr.(inject @@ econstr "pair" [ econstr "aab" []; econstr "bbb" [] ]) in
  let t1 = Typs.(inject @@ construct @@ T [ ("pair", [ T [ ("aab", []) ]; T [ ("bbb", []) ] ]) ]) in
  runR EvalMRez.reifier EvalMRez.show EvalMRez.show_logic 1 q qh ("test1 eval_m", fun q ->
     eval_m e1 t1 Matchable.(inject Scru) q
  );
  runR EvalMRez.reifier EvalMRez.show EvalMRez.show_logic 1 q qh ("test1 eval_m", fun q ->
     eval_m e1 t1 Matchable.(inject (Field (Z, Scru))) q
  );

  let open Main_inputs in
  runR EvalMRez.reifier EvalMRez.show EvalMRez.show_logic 1 q qh
    ("test1 S[1][0]", fun q ->
       eval_m
        Expr.(
          let l = econstr "succ" [econstr "succ" [econstr "zero" []]] in
          let r = l in
          inject @@ econstr "pair"  [ l; r ])
        ArgPeanoSimple.typs Matchable.(inject (Field (Z, Field (S Z, Scru)))) q
  );

  ()
*)

open Main_inputs



(*

module N0 = Impl1.Make(struct
  include ArgMake(ArgSimpleList)
end)

let () = N0.test ()
*)
(*
module N1 = Impl1.Make(struct
  include ArgMake(ArgTwoNilShort)
end)*)

(*let () = N1.test ()*)
(*
module N2 = Impl1.Make(struct
  include ArgMake(ArgTwoNilLonger)
end)
*)
(*let () = N2.test ()*)






(*
module M1 = TwoNilList2(struct
  (* let msg = "simple list" *)
  include ArgMake(ArgSimpleList)
end)

module M2 = TwoNilList2(struct
  (* let msg = "ideal_IR 0.5 minimal hacks" *)
  include ArgMake(ArgTwoNilShort)
end)

let () = M1.test ()
let () = M2.test ()
*)



module FTrueFalse = Algo_fair.Make(struct
  include ArgMake(ArgTrueFalse)
end)
let () = FTrueFalse.test (-1)



module FPairTrueFalse = Algo_fair.Make(struct
  include ArgMake(ArgPairTrueFalse)
  let max_ifs_count = 2
end)
(*let () = FPairTrueFalse.test (-1)*)

module FABC = Algo_fair.Make(struct
  include ArgMake(ArgABC)

  (* in this demo merging cases can be helpful *)
end)
(*let () = FABC.test 10*)



module Peano = Algo_fair.Make(struct
  include ArgMake(ArgPeanoSimple)
  let shortcut tag _ rez =
    fresh ()
      (rez === !!true)
      (tag =/= !!(tag_of_string_exn "pair"))
end)

let () = Peano.test 10


(* *************************************************************************** *)
module FairLists1 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
end)

let () = FairLists1.test 10

module FairLists2 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
  (* adding non-pair shourtcut optimizes from 1.8 (for all answers) to 1.4 (for all answers) *)
  let shortcut tag _ rez =
    fresh ()
      (rez === !!true)
      (tag =/= !!(tag_of_string_exn "pair"))

  let info = info ^ " + (=/= pair)"
end)

(*let () = FairLists2.test 10*)


module F2NilShort = Algo_fair.Make(struct
  include ArgMake(ArgTwoNilLists2Cons)
end)

(* There are only 4 answers here*)
(*let () = F2NilShort.test (4)*)


(* ************************************************************************** *)
module WWW = Algo_fair.Make(struct
  include ArgMake(ArgTwoNilLists2Simplified)
end)
let () = WWW.test 10


module WWW2 = Algo_fair.Make(struct
  include ArgMake(ArgTwoNilLists2Simplified)

  let info = info ^ "+ max_height=2 + check_repeated_ifs"
end)
(*let () = WWW2.test ~check_repeated_ifs:true 10*)


(* ************************************************************************** *)
module XXX = Algo_fair.Make(struct
  include ArgMake(ArgTwoNilLists2Simplified)
  let shortcut tag _ rez =
    fresh ()
      (rez === !!true)
      (tag =/= !!(tag_of_string_exn "pair"))

(*  let max_height = 2*)
  let info = info ^ " + tag=/=pair"
end)

let () = XXX.test 10

(* ************************************************************************** *)

module XXX2 = Algo_fair.Make(struct
  include ArgMake(ArgTwoNilLists2Simplified)
  let shortcut tag _ rez =
    fresh ()
      (rez === !!true)
      (tag =/= !!(tag_of_string_exn "pair"))

  let info = info ^ " + tag=/=pair + check_repeated_ifs"

  let ir_hint ir =
    print_endline "applying hint";
    let open Std in
    fresh (c tl def)
      (ir === IR.switch (Matchable.field1 ())
                ((Std.Pair.pair !!(tag_of_string_exn "cons") c)%tl)
                def)

end)

(*let () = XXX2.test ~check_repeated_ifs:true 10*)

(* ************************************************************************** *)

(*let () = Fair4_1.test 20*)

(*module F1 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
  let max_ifs_count = 2
end)

module Fair2_1 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
end)*)

(*
module Fair2_2 = Algo_fair2.Make(struct
  include ArgMake(ArgTwoNilShort)
end)
*)

(*let () = Fair2_1.test 10*)
(*let () = Fair2_2.test ~n:2*)
