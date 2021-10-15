open GT
open OCanren
open OCanren.Std
open Work_base_common

let nat_lt a b q221 =
  let rec helper root q216 =
    conde
      [ fresh q217 (root === pair q217 (z ())) (q216 === !!false)
      ; fresh q219 (root === pair (z ()) (s q219)) (q216 === !!true)
      ; fresh (x y) (root === pair (s x) (s y)) (helper (pair x y) q216)
      ]
  in
  helper (pair a b) q221
;;

let nat_leq a b q215 =
  let rec helper root q210 =
    conde
      [ fresh q211 (root === pair (z ()) q211) (q210 === !!true)
      ; fresh q213 (root === pair (s q213) (z ())) (q210 === !!false)
      ; fresh (x y) (root === pair (s x) (s y)) (helper (pair x y) q210)
      ]
  in
  helper (pair a b) q215
;;

let fst z q207 = fresh (a q208) (z === pair a q208) (a === q207)
let snd z q204 = fresh (q205 b) (z === pair q205 b) (b === q204)

let rec list_mem x xs q196 =
  xs
  === nil ()
  &&& (q196 === !!false)
  ||| fresh
        (h tl q199)
        (xs === h % tl)
        (conde [ x === h &&& (q199 === !!true); q199 === !!false &&& (x =/= h) ])
        (conde
           [ q199 === !!true &&& (q196 === !!true)
           ; q199 === !!false &&& list_mem x tl q196
           ])
;;

let rec list_assoc name ys q189 =
  fresh
    (k v xs q191)
    (ys === pair k v % xs)
    (conde [ k === name &&& (q191 === !!true); q191 === !!false &&& (k =/= name) ])
    (conde
       [ q191 === !!true &&& (v === q189); q191 === !!false &&& list_assoc name xs q189 ])
;;

let list_map_all f =
  let rec helper xs q183 =
    xs
    === nil ()
    &&& (q183 === !!true)
    ||| fresh
          (y ys q186)
          (xs === y % ys)
          (f y q186)
          (fresh q187 (q186 === some q187) (helper xs q183)
          ||| (q186 === none () &&& (q183 === !!false)))
  in
  helper
;;

let list_map f xs q182 =
  let rec helper xs q176 =
    xs
    === nil ()
    &&& (q176 === nil ())
    ||| fresh
          (x q178 q179 q180)
          (xs === x % q178)
          (q176 === q179 % q180)
          (f x q179)
          (helper q178 q180)
  in
  helper xs q182
;;

let list_mapi f xs q175 =
  let rec helper i xs q169 =
    xs
    === nil ()
    &&& (q169 === nil ())
    ||| fresh
          (x q171 q172 q173)
          (xs === x % q171)
          (q169 === q172 % q173)
          (f i x q172)
          (helper (s i) q171 q173)
  in
  helper (z ()) xs q175
;;

let rec list_all f xs q163 =
  xs
  === nil ()
  &&& (q163 === !!true)
  ||| fresh
        (x q165 q167)
        (xs === x % q165)
        (f x q167)
        (conde
           [ q167 === !!true &&& list_all f q165 q163
           ; q167 === !!false &&& (q163 === !!false)
           ])
;;

let rec list_all2 f xs0 ys0 q150 =
  fresh
    q151
    (q151 === pair xs0 ys0)
    (conde
       [ fresh
           (x xs y ys q153)
           (q151 === pair (x % xs) (y % ys))
           (f x y q153)
           (conde
              [ q153 === !!true &&& list_all2 f xs ys q150
              ; q153 === !!false &&& (q150 === !!false)
              ])
       ; q151 === pair (nil ()) (nil ()) &&& (q150 === !!true)
       ; fresh (q156 q157) (q151 === pair (q156 % q157) (nil ())) (q150 === !!false)
       ; fresh (q159 q160) (q151 === pair (nil ()) (q159 % q160)) (q150 === !!false)
       ])
;;

let rec same_length xs ys q138 =
  fresh
    q139
    (q139 === pair xs ys)
    (conde
       [ fresh
           (q140 xs q141 ys)
           (q139 === pair (q140 % xs) (q141 % ys))
           (same_length xs ys q138)
       ; fresh (q142 q143) (q139 === pair (nil ()) (q142 % q143)) (q138 === !!false)
       ; fresh (q145 q146) (q139 === pair (q145 % q146) (nil ())) (q138 === !!false)
       ; q139 === pair (nil ()) (nil ()) &&& (q138 === !!true)
       ])
;;

let rec list_combine xs ys q132 =
  fresh
    q133
    (q133 === pair xs ys)
    (q133
    === pair (nil ()) (nil ())
    &&& (q132 === nil ())
    ||| fresh
          (x xs y ys q135)
          (q133 === pair (x % xs) (y % ys))
          (q132 === pair x y % q135)
          (list_combine xs ys q135))
;;

let rec list_foldl f acc ys q128 =
  ys
  === nil ()
  &&& (acc === q128)
  ||| fresh (x xs q130) (ys === x % xs) (f acc x q130) (list_foldl f q130 xs q128)
;;

let list_decorate_nat xs q126 =
  fresh q125 (list_mapi (fun i x q127 -> i === q127) xs q125) (list_combine q125 xs q126)
;;

let rec list_nth_nat idx xs q119 =
  fresh
    q120
    (q120 === pair idx xs)
    (fresh (x q121) (q120 === pair (z ()) (x % q121)) (x === q119)
    ||| fresh (n q123 xs) (q120 === pair (s n) (q123 % xs)) (list_nth_nat n xs q119))
;;

let rec match1pat s p q100 =
  fresh
    q101
    (q101 === pair s p)
    (fresh q102 (q101 === pair q102 (wildCard ())) (q100 === !!true)
    ||| fresh
          (tag1 es tag2 ps q105 q109 q110)
          (q101 === pair (eConstr tag1 es) (pConstr tag2 ps))
          (conde
             [ tag1 === tag2 &&& (q109 === !!true); q109 === !!false &&& (tag1 =/= tag2) ])
          (same_length ps es q110)
          (conde
             [ q109 === !!false &&& (q105 === !!false)
             ; q109 === !!true &&& (q105 === q110)
             ])
          (conde
             [ fresh
                 pairs
                 (q105 === !!true)
                 (list_combine ps es pairs)
                 (list_all
                    (fun z q107 -> fresh (p e) (z === pair p e) (match1pat e p q107))
                    pairs
                    q100)
             ; q105 === !!false &&& (q100 === !!false)
             ]))
;;

let rec eval_pat s pats q95 =
  pats
  === nil ()
  &&& (q95 === none ())
  ||| fresh
        (p rhs ps q98)
        (pats === pair p rhs % ps)
        (match1pat s p q98)
        (conde
           [ q98 === !!true &&& (q95 === some rhs)
           ; q98 === !!false &&& eval_pat s ps q95
           ])
;;

let rec eval_pat_hacky s on_fail pats q94 =
  let rec helper acc pats q83 =
    pats
    === nil ()
    &&& (on_fail === q83)
    ||| fresh
          (p rhs ps q86)
          (pats === pair p rhs % ps)
          (match1pat s p q86)
          (conde
             [ fresh
                 q88
                 (q86 === !!true)
                 (q88 === !!true)
                 (rhs === q83)
                 (list_all
                    (fun p q91 ->
                      fresh
                        q90
                        (match1pat s p q90)
                        (conde
                           [ q90 === !!true &&& (q91 === !!false)
                           ; q90 === !!false &&& (q91 === !!true)
                           ]))
                    acc
                    q88)
             ; q86 === !!false &&& helper (p % acc) ps q83
             ])
  in
  helper (nil ()) pats q94
;;

let tinfo_names tt q82 = fresh xs (tt === t xs) (list_map fst xs q82)
let tinfo_args tt name q81 = fresh xs (tt === t xs) (list_assoc name xs q81)
let tinfo_nth_arg tt n q80 = fresh xs (tt === t xs) (list_nth_nat n xs q80)
let info_assoc tt name q79 = fresh xs (tt === t xs) (list_assoc name xs q79)

let rec well_typed_expr e0 typs0 q75 =
  fresh
    (q76 tag es ts arg_infos)
    (q76 === pair e0 typs0)
    (q76 === pair (eConstr tag es) ts)
    (info_assoc typs0 tag arg_infos)
    (list_all2 well_typed_expr es arg_infos q75)
;;

let rec height_of_matchable root q70 =
  root
  === scru ()
  &&& (q70 === s (z ()))
  ||| fresh
        (q72 ss q73)
        (root === field q72 ss)
        (q70 === s q73)
        (height_of_matchable ss q73)
;;

let matchable_leq_nat m n q69 =
  let rec helper root q61 =
    conde
      [ root === pair (scru ()) (z ()) &&& (q61 === !!false)
      ; fresh q63 (root === pair (scru ()) (s q63)) (q61 === !!true)
      ; fresh (q65 m1 n1) (root === pair (field q65 m1) (s n1)) (helper (pair m1 n1) q61)
      ; fresh (q66 q67) (root === pair (field q66 q67) (z ())) (q61 === !!false)
      ]
  in
  helper (pair m n) q69
;;

let rec eval_m s typinfo0 path0 q60 =
  let rec helper path q48 =
    conde
      [ path === scru () &&& (q48 === pair s typinfo0)
      ; fresh
          (nth scru q51 cname es next_tinfos arg_info q53 q54)
          (path === field nth scru)
          (q51 === pair (eConstr cname es) next_tinfos)
          (q48 === pair q53 q54)
          (helper scru q51)
          (info_assoc next_tinfos cname arg_info)
          (list_nth_nat nth es q53)
          (list_nth_nat nth arg_info q54)
      ]
  in
  fresh
    (q57 ans info q58)
    (q57 === pair ans info)
    (q60 === pair ans q58)
    (helper path0 q57)
    (tinfo_names info q58)
;;

let rec not_in_history x xs q40 =
  xs
  === nil ()
  &&& (q40 === !!true)
  ||| fresh
        (h tl q43)
        (xs === h % tl)
        (conde [ x === h &&& (q43 === !!true); q43 === !!false &&& (x =/= h) ])
        (q43
        === !!false
        &&& not_in_history x tl q40
        ||| (q43 === !!true &&& (q40 === !!false)))
;;

let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag ir q39 =
  let open Unn_pre in
  let rec inner history test_list irrr q0 =
    conde
      [ irrr === fail () &&& (q0 === none ())
      ; fresh n (irrr === lit n) (q0 === some n)
      ; fresh
          (m cases on_default q4 q17 etag args cnames)
          (irrr === switch m cases on_default)
          (debug_var m (Unn_pre.flip Unn_pre.Matchable.reify) (fun xs ->
               Format.printf
                 "Going to eval matchable: %a\n%!"
                 (GT.fmt Matchable.logic)
                 (Caml.List.hd xs);
               success))
          (q17 === pair (eConstr etag args) cnames)
          (eval_m s tinfo m q17)
          (shortcut0 m max_height cases q4)
          (conde
             [ fresh
                 ()
                 (q4 === missExample ())
                 (debug_var on_default (Unn_pre.flip Unn_pre.IR.reify) (fun xs ->
                      Format.printf
                        "Going to eval default branch: %a\n%!"
                        IR.fmt_logic
                        (Caml.List.hd xs);
                      success))
                 (inner history test_list on_default q0)
                 (debug_var
                    (Std.pair on_default q0)
                    (Unn_pre.flip
                    @@ Std.Pair.reify IR.reify (Std.Option.reify OCanren.reify))
                    (function
                      | [ Value (ir, Value (Some (Value n))) ] ->
                        Format.printf "\t%a ~~~> %d\n%!" IR.fmt_logic ir n;
                        success
                      | [ Value (_, v) ] ->
                        Format.printf
                          "The answer in the default branch is %s\n%!"
                          (GT.show
                             OCanren.logic
                             (GT.show GT.option (GT.show OCanren.logic @@ GT.show GT.int))
                             v);
                        success
                      | _ ->
                        let _ = assert false in
                        success))
                 (debug_var s (Unn_pre.flip Expr.reify) (function
                     | [] -> assert false
                     | scrus ->
                       Caml.List.iteri
                         (fun i s ->
                           Format.printf "\t  scru_%d = %a \n%!" i Expr.pp_logic s)
                         scrus;
                       success))
                 (list_all
                    (fun br q10 ->
                      fresh
                        (q9 br_tag br_rhs)
                        (br === Std.pair br_tag br_rhs)
                        (inner history test_list br_rhs q9)
                        (conde
                           [ q0 === q9 &&& (q10 === !!true)
                           ; q10 === !!false &&& (q0 =/= q9)
                           ]))
                    cases
                    !!true)
             ; fresh
                 ()
                 (q4 === goodSubTree ())
                 (shortcut1 etag m cases history !!true)
                 (test_list (m % history) etag cnames on_default cases q0)
             ])
      ]
  in
  let rec test_list next_histo etag cnames on_default cases0 q37 =
    let rec helper constr_names cases q20 =
      fresh
        q21
        (conde
           [ cases === nil () &&& (q21 === !!true)
           ; q21 === !!false &&& (cases =/= nil ())
           ])
        (q21
        === !!true
        &&& inner next_histo test_list on_default q20
        ||| fresh
              (constr_hd constr_tl qtag ontag clauses_tl q25)
              (q21 === !!false)
              (constr_names === constr_hd % constr_tl)
              (cases === pair qtag ontag % clauses_tl)
              (conde
                 [ qtag === constr_hd &&& (q25 === !!true)
                 ; q25 === !!false &&& (qtag =/= constr_hd)
                 ])
              (fresh
                 q27
                 (q25 === !!true)
                 (conde
                    [ qtag === etag &&& (q27 === !!true)
                    ; q27 === !!false &&& (qtag =/= etag)
                    ])
                 (q27
                 === !!true
                 &&& inner next_histo test_list ontag q20
                 ||| (q27 === !!false &&& helper constr_tl clauses_tl q20))
              ||| (q25 === !!false &&& helper constr_tl cases q20)))
    in
    helper cnames cases0 q37
  in
  fresh
    ()
    (debug_var ir (Unn_pre.flip Unn_pre.IR.reify) (function
        | [ p ] ->
          Format.printf "Going to eval program\n@[%a@]\n%!" IR.fmt_logic p;
          success
        | _ -> assert false))
    (inner (nil ()) test_list ir q39)
;;
