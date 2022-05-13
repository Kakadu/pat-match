open Main_inputs
open Unn_pre
open OCanren
open Tester
module W = Work_matchable_kind
module Arg = Main_inputs.ArgMake (Main_inputs.ArgPairTrueFalse)

module E = struct
  open OCanren.Std

  let pair a b = Expr.constr !!(Tag.inttag_of_string_exn "pair") (a %< b)

  let triple a b c =
    Expr.constr !!(Tag.inttag_of_string_exn "triple") (a % (b %< c))

  let true_ = Expr.constr !!(Tag.inttag_of_string_exn "true") (nil ())
  let false_ = Expr.constr !!(Tag.inttag_of_string_exn "false") (nil ())
end

module GroundField = struct
  open Matchable

  let scru = Scru
  let field0 : ground = Field (N.Z, Scru)
  let field1 : ground = Field (N.(S Z), Scru)
  let field2 : ground = Field (N.(S (S Z)), Scru)
end

let _0 : IR.injected = IR.int !!0
let _1 : IR.injected = IR.int !!1
let _2 : IR.injected = IR.int !!2
let _3 : IR.injected = IR.int !!3

let default_shortcut0 good_matchables m max_height cases rez =
  let open OCanren in
  fresh ()
    (W.matchable_leq_nat m max_height !!true)
    (cases =/= Std.nil ())
    (debug "inside default_shortcut0")
    (debug_var m Matchable.reify (fun ms ->
         let set = Matchable.Set.of_list ms in
         if Matchable.Set.is_empty set then failure
         else
           let ms = Matchable.Set.min_elt set in
           (* match Stdlib.List. ms with
              | [] -> failure
              | _ :: _ :: _ ->
                  Format.printf "default_shortcut0 on matchable %s\n%!"
                    ((GT.show GT.list) Matchable.show_logic ms);
                  failwith "too many answers" *)
           match Matchable.to_ground ms with
           | None ->
               Format.printf "non-ground matchable is %a\n%!"
                 (GT.fmt Matchable.logic) ms;
               success
           | Some Matchable.Scru -> failure
           | Some m when List.mem m good_matchables ->
               rez === MatchableKind.good
           | Some _m -> rez === MatchableKind.miss_example))

let default_shortcut _etag m _cases history _typs _rez =
  let open OCanren in
  W.not_in_history m history !!true &&& success

let default_shortcut_tag etag constr_names rez =
  let open OCanren in
  let open OCanren.Std in
  fresh () (rez === !!true)
    (debug_var constr_names (Std.List.reify OCanren.reify) (function
      | [ lst ] -> (
          try
            let ground_list =
              Std.List.prj_exn
                (function Value x -> x | _ -> raise OCanren.Not_a_value)
                lst
              |> Std.List.to_list Fun.id
            in
            fresh () (OCanren.FD.domain etag ground_list)
          with OCanren.Not_a_value ->
            Format.eprintf "Not_a_value when reifying type names. Skip\n%!";
            success)
      | _ -> assert false))

let default_shortcut4 (t1 : Tag.injected) t2 rez =
  fresh flag
    (debug_var (Triple.make t1 t2 rez)
       (Triple.reify Tag.reify Tag.reify OCanren.reify) (function
      | [ Value (t1, t2, Var (n, _)) ] ->
          let __ _ =
            Format.printf "default_shortcut4 of (%s, %s, _.%d)\n%!"
              (Tag.show_logic t1) (Tag.show_logic t2) n
          in
          success
      | _ -> assert false))
    (OCanren.unif_hack t1 t2 flag)
    (conde
       [
         flag =/= !!true &&& (rez === !!true);
         flag =/= !!false &&& (rez === !!false);
       ])

let run_int eta =
  runR OCanren.reify (GT.show GT.int)
    (GT.show OCanren.logic @@ GT.show GT.int)
    eta

let run_ir eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  runR IR.reify IR.show IR.show_logic eta

(* *********************************************************** *)

(*
  match ... with
  | true  -> 0
  | _ -> 1


  q=(switch S with
    | true -> 0
    | _ -> 1)

  *)

let program : IR.injected -> _ =
 fun q ->
  let open OCanren.Std in
  let scru = Matchable.scru () in
  let ite cond c th el = IR.switch cond !<(Std.pair c th) el in
  let ttrue = !!(Tag.of_string_exn "true") in
  let tfalse = !!(Tag.of_string_exn "false") in
  fresh () (q === ite scru ttrue _0 _1)

let examples =
  let open E in
  [
    (0, (fun q -> fresh () (q === true_)), GroundField.[ scru ]);
    (* (1, (fun q -> fresh () (q =/= true_)), GroundField.[ scru ]); *)
    (1, (fun q -> fresh () (q === false_)), GroundField.[ scru ]);
  ]

let eval_ir_pairs ~fields scru ir rez =
  let shortcut0 good_matchables m max_height cases rez =
    let open OCanren in
    fresh ()
      (W.matchable_leq_nat m max_height !!true)
      (cases =/= Std.nil ())
      (debug_var m Matchable.reify (fun ms ->
           match ms with
           | [] -> failure
           | _ :: _ :: _ -> failwith "too many answers"
           | [ ms ] -> (
               match Matchable.to_ground ms with
               | None -> success
               | Some m when List.mem m good_matchables ->
                   rez === MatchableKind.good
               | Some _m -> rez === MatchableKind.miss_example)))
  in
  fresh max_height
    (max_height === N.(inject @@ of_int 1))
    (Work_matchable_kind.eval_ir scru max_height
       (Typs.inject ArgTrueFalse.typs)
       (shortcut0 fields) default_shortcut default_shortcut_tag
       default_shortcut4 ir rez)

let test_example ~fields n init_scru =
  run_int 3 q qh
    ( Format.sprintf "===== Running forward example %d in PairSuperSimple test" n,
      fun rhs ->
        fresh (scru ir rez)
          (rez === Std.Option.some rhs)
          (program ir) (init_scru scru)
          (eval_ir_pairs ~fields scru ir rez)
          (debug_var scru Expr.reify (function xs ->
               List.iteri
                 (fun n q -> Format.printf "\t%d: %s\n%!" n (Expr.show_logic q))
                 xs;
               success)) )

let __ _ =
  let _, x, fields = List.nth examples 0 in
  test_example ~fields 0 x

let __ _ =
  let _, x, fields = List.nth examples 1 in
  test_example ~fields 1 x

let _ =
  run_ir 1 q qh
    (REPR
       (fun ir ->
         fresh ()
           (List.fold_left
              (fun acc (rhs, init_scru, fields) ->
                fresh (scru rez)
                  (rez === Std.Option.some !!rhs)
                  acc (init_scru scru)
                  (eval_ir_pairs ~fields scru ir rez))
              success
              [ List.nth examples 0; List.nth examples 1 ])))

let __ _ =
  let open Work_matchable_kind in
  let open Std in
  let goal q =
    fresh (a b a2 b2 a3 b3 ir)
      (q === Std.pair a b % (Std.pair a2 b2 % (Std.pair a3 b3 % Std.nil ())))
      (dirty_hack q (Std.some !!1) ir ~f:(fun _ rhs rez ->
           conde [ rhs === rez; rhs === rez ]))
  in
  runR
    (Std.List.reify (Std.Pair.reify OCanren.reify OCanren.reify))
    ([%show: (GT.string, GT.int) Std.Pair.ground Std.List.ground] ())
    ([%show:
       (GT.string OCanren.logic, GT.int OCanren.logic) Std.Pair.logic
       Std.List.logic] ())
    1 q qh ("", goal)
