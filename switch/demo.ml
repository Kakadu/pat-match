open Main_inputs
open Unn_pre
open OCanren
open Tester
module W = Unn_pre.WorkHO
module Arg = Main_inputs.ArgMake (Main_inputs.ArgPairTrueFalse)

module E = struct
  open OCanren.Std

  let pair a b = Expr.constr !!(Tag.inttag_of_string_exn "pair") (a %< b)
  let triple a b c = Expr.constr !!(Tag.inttag_of_string_exn "triple") (a % (b %< c))
  let true_ = Expr.constr !!(Tag.inttag_of_string_exn "true") (nil ())
  let false_ = Expr.constr !!(Tag.inttag_of_string_exn "false") (nil ())
end

let default_shortcut0 m max_height cases rez =
  let open OCanren in
  fresh
    ()
    (debug_var m (flip Matchable.reify) (fun ms ->
         (*        Format.printf "default_shortcut0 on matchable %s\n%!" ((GT.show GT.list) Matchable.show_logic ms);*)
         match ms with
         | [] -> failure
         | _ :: _ :: _ -> failwith "too many answers"
         | [ ms ] ->
           (match Matchable.to_ground ms with
           | None -> success
           | Some Matchable.Scru -> failure
           | Some _m -> success)))
    (W.matchable_leq_nat m max_height !!true)
    (cases =/= Std.nil ())
    (rez === !!true)
;;

let default_shortcut _etag m _cases history _rez =
  let open OCanren in
  W.not_in_history m history !!true &&& success
;;

let default_shortcut_tag constr_names cases _rez =
  let open OCanren in
  let open OCanren.Std in
  conde
    [ constr_names === nil () &&& failure
    ; fresh u (constr_names === u % nil ()) (cases === nil ())
    ; fresh (u v w) (constr_names === u % (v % w))
    ]
;;

let __ _ =
  let printed_clauses = Format.printf "%a\n%!" Clauses.pretty_print Arg.clauses in
  let injected_clauses = Clauses.inject Arg.clauses in
  runR
    IR.reify
    IR.show
    IR.show_logic
    (-1)
    q
    qh
    (REPR
       (fun ans ->
         let open OCanren.Std in
         fresh
           scru
           (scru === Expr.constr !!(Tag.inttag_of_string_exn "pair") (E.false_ %< E.true_))
           (W.eval_pat scru injected_clauses (Std.Option.some ans))));
  ()
;;

let run_expr eta = runR Expr.reify Expr.show Expr.show_logic eta

let _ =
  run_expr
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e =/= E.pair E.true_ __) (e =/= E.pair __ E.true_)))
;;

let _ =
  run_expr
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e === E.(pair __ true_)) (e =/= E.(pair true_ __))))
;;

let run_pair eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  runR
    (Std.Pair.reify OCanren.reify OCanren.reify)
    (GT.show Std.Pair.ground show_int show_int)
    (GT.show Std.Pair.logic sl sl)
    eta
;;

let run_ir eta =
  let show_int = GT.show GT.bool in
  let sl = GT.show OCanren.logic show_int in
  runR IR.reify IR.show IR.show_logic eta
;;

let __ _ =
  run_pair
    (-1)
    q
    qh
    (REPR (fun e -> fresh () (e =/= Std.pair !!true __) (e =/= Std.pair __ !!true)))
;;

(*

match ... with
| pair (true, _) -> 1
| pair (_, true) -> 1
| pair (false, false) -> 0

*)
let _ =
  let examples =
    [ (* (fun q -> q === E.(pair true_ __)), 1
    ; (fun q -> fresh () (q === E.(pair __ true_)) (q =/= E.(pair true_ __))), 2
    ; *)
      (fun q -> q === E.(pair __ true_)), 1
    ; (fun q -> fresh () (q === E.(pair true_ __)) (q =/= E.(pair __ true_))), 2
    ; ( (fun q ->
          fresh
            ()
            (q === E.(pair false_ false_))
            (q =/= E.(pair true_ __))
            (q =/= E.(pair __ true_)))
      , 3 )
    ]
  in
  run_ir
    3
    q
    qh
    (REPR
       (fun ir ->
         fresh
           (max_height tinfo)
           (max_height === N.(inject @@ of_int 2))
           (List.fold_left
              (fun acc (desc, rhs) ->
                fresh
                  (scru rez)
                  (rez === Std.Option.some !!rhs)
                  acc
                  (desc scru)
                  (W.eval_ir
                     scru
                     max_height
                     tinfo
                     default_shortcut0
                     default_shortcut
                     default_shortcut_tag
                     ir
                     rez))
              success
              examples)))
;;

(*

match ... with
| triple (_, false, true) -> 1
| triple (false, true, _) -> 2
| triple (_, _, false) -> 3
| triple (_, _, true) -> 4

*)
let __ _ =
  let examples =
    let open E in
    [ (fun q -> q === triple __ false_ true_), 1
    ; (fun q -> fresh () (q === triple false_ true_ __) (q =/= triple __ false_ true_)), 2
    ; ( (fun q ->
          fresh
            ()
            (q === triple __ __ false_)
            (q =/= triple false_ true_ __)
            (q =/= triple __ false_ true_))
      , 3 )
    ; ( (fun q ->
          fresh
            ()
            (q === triple __ __ true_)
            (q =/= triple __ __ false_)
            (q =/= triple false_ true_ __)
            (q =/= triple __ false_ true_))
      , 4 )
    ]
  in
  run_ir
    3
    q
    qh
    (REPR
       (fun ir ->
         fresh
           (max_height tinfo)
           (max_height === N.(inject @@ of_int 2))
           (List.fold_left
              (fun acc (desc, rhs) ->
                fresh
                  (scru rez)
                  (rez === Std.Option.some !!rhs)
                  (tinfo === Typs.inject Main_inputs.ArgTripleBool.typs)
                  acc
                  (desc scru)
                  (W.eval_ir
                     scru
                     max_height
                     tinfo
                     default_shortcut0
                     default_shortcut
                     default_shortcut_tag
                     ir
                     rez))
              success
              examples)))
;;
