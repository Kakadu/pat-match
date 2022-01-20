open GT
open OCanren
open OCanren.Std
open Work_base_common
open Unn_pre

let debug_lino _line _num =
  fresh
    q
    (debug_var q OCanren.reify (function _ ->
         (* Format.printf "%s %d\n%!" line num; *)
         success))
;;

let nat_lt a b q235 =
  let rec helper root q230 =
    conde
      [ fresh q231 (root === pair q231 (z ())) (q230 === !!false)
      ; fresh q233 (root === pair (z ()) (s q233)) (q230 === !!true)
      ; fresh (x y) (root === pair (s x) (s y)) (helper (pair x y) q230)
      ]
  in
  helper (pair a b) q235
;;

let nat_leq a b q229 =
  let rec helper root q224 =
    conde
      [ fresh q225 (root === pair (z ()) q225) (q224 === !!true)
      ; fresh q227 (root === pair (s q227) (z ())) (q224 === !!false)
      ; fresh
          (x y)
          (root === pair (s x) (s y))
          (debug_lino __FILE__ __LINE__)
          (helper (pair x y) q224)
      ]
  in
  helper (pair a b) q229
;;

let fst z q221 = fresh (a q222) (z === pair a q222) (a === q221)
let snd z q218 = fresh (q219 a) (z === pair q219 a) (a === q218)

let rec list_mem x xs q210 =
  conde
    [ xs === nil () &&& (q210 === !!false)
    ; fresh
        (h tl)
        (debug_lino __FILE__ __LINE__)
        (xs === h % tl)
        (conde [ x === h &&& (q210 === !!true); x =/= h &&& list_mem x tl q210 ])
    ]
;;

let rec list_assoc name ys q203 =
  fresh
    (k v xs q205)
    (ys === pair k v % xs)
    (conde [ k === name &&& (q205 === !!true); q205 === !!false &&& (k =/= name) ])
    (conde
       [ q205 === !!true &&& (v === q203); q205 === !!false &&& list_assoc name xs q203 ])
;;

let list_map_all f =
  let rec helper xs q197 =
    conde
      [ xs === nil () &&& (q197 === !!true)
      ; fresh
          (y ys q200)
          (xs === y % ys)
          (f y q200)
          (conde
             [ fresh
                 q201
                 (q200 === some q201)
                 (debug_lino __FILE__ __LINE__)
                 (helper xs q197)
             ; q200 === none () &&& (q197 === !!false)
             ])
      ]
  in
  helper
;;

let list_map f xs q196 =
  let rec helper xs q190 =
    conde
      [ xs === nil () &&& (q190 === nil ())
      ; fresh
          (x q192 q193 q194)
          (xs === x % q192)
          (q190 === q193 % q194)
          (f x q193)
          (debug_lino __FILE__ __LINE__)
          (helper q192 q194)
      ]
  in
  helper xs q196
;;

let list_mapi f xs q189 =
  let rec helper i xs q183 =
    conde
      [ xs === nil () &&& (q183 === nil ())
      ; fresh
          (x q185 q186 q187)
          (xs === x % q185)
          (q183 === q186 % q187)
          (f i x q186)
          (debug_lino __FILE__ __LINE__)
          (helper (s i) q185 q187)
      ]
  in
  helper (z ()) xs q189
;;

let rec list_all f xs q177 =
  conde
    [ xs === nil () &&& (q177 === !!true)
    ; fresh
        (x q179 q181)
        (xs === x % q179)
        (f x q181)
        (conde
           [ q181 === !!true &&& debug_lino __FILE__ __LINE__ &&& list_all f q179 q177
           ; q181 === !!false &&& (q177 === !!false)
           ])
    ]
;;

let rec list_all2 f xs0 ys0 q164 =
  fresh
    q165
    (q165 === pair xs0 ys0)
    (conde
       [ fresh
           (x xs y ys q167)
           (q165 === pair (x % xs) (y % ys))
           (f x y q167)
           (conde
              [ q167
                === !!true
                &&& debug_lino __FILE__ __LINE__
                &&& list_all2 f xs ys q164
              ; q167 === !!false &&& (q164 === !!false)
              ])
       ; q165 === pair (nil ()) (nil ()) &&& (q164 === !!true)
       ; fresh (q170 q171) (q165 === pair (q170 % q171) (nil ())) (q164 === !!false)
       ; fresh (q173 q174) (q165 === pair (nil ()) (q173 % q174)) (q164 === !!false)
       ])
;;

let rec same_length xs ys q152 =
  fresh
    q153
    (q153 === pair xs ys)
    (conde
       [ fresh
           (q154 xs q155 ys)
           (q153 === pair (q154 % xs) (q155 % ys))
           (debug_lino __FILE__ __LINE__)
           (same_length xs ys q152)
       ; fresh (q156 q157) (q153 === pair (nil ()) (q156 % q157)) (q152 === !!false)
       ; fresh (q159 q160) (q153 === pair (q159 % q160) (nil ())) (q152 === !!false)
       ; q153 === pair (nil ()) (nil ()) &&& (q152 === !!true)
       ])
;;

let rec list_combine xs ys q146 =
  fresh
    q147
    (q147 === pair xs ys)
    (conde
       [ q147 === pair (nil ()) (nil ()) &&& (q146 === nil ())
       ; fresh
           (x xs y ys q149)
           (q147 === pair (x % xs) (y % ys))
           (q146 === pair x y % q149)
           (debug_lino __FILE__ __LINE__)
           (list_combine xs ys q149)
       ])
;;

let rec list_foldl f acc ys q142 =
  conde
    [ ys === nil () &&& (acc === q142)
    ; fresh
        (x xs q144)
        (ys === x % xs)
        (f acc x q144)
        (debug_lino __FILE__ __LINE__)
        (list_foldl f q144 xs q142)
    ]
;;

let list_decorate_nat xs q140 =
  fresh q139 (list_mapi (fun i _x q141 -> i === q141) xs q139) (list_combine q139 xs q140)
;;

let rec list_nth_nat idx xs q133 =
  fresh
    q134
    (q134 === pair idx xs)
    (conde
       [ fresh (x q135) (q134 === pair (z ()) (x % q135)) (x === q133)
       ; fresh
           (n q137 xs)
           (q134 === pair (s n) (q137 % xs))
           (debug_lino __FILE__ __LINE__)
           (list_nth_nat n xs q133)
       ])
;;

let rec list_length xs rez =
  conde
    [ xs === nil () &&& (rez === z ())
    ; fresh
        (q130 tl q131)
        (xs === q130 % tl)
        (rez === s q131)
        (* (debug_var rez (flip N.reify) (function
            | [ n ] ->
              Format.printf "%s\n%!" (N.show_logic n);
              success
            | _ -> assert false)) *)
        (* (debug_lino __FILE__ __LINE__) *)
        (list_length tl q131)
    ]
;;

let rec match1pat s p q109 =
  fresh
    q110
    (q110 === pair s p)
    (fresh q111 (q110 === pair q111 (wildCard ())) (q109 === !!true)
    ||| fresh
          (tag1 es tag2 ps q114 q118 q119)
          (q110 === pair (eConstr tag1 es) (pConstr tag2 ps))
          (conde
             [ tag1 === tag2 &&& (q118 === !!true); q118 === !!false &&& (tag1 =/= tag2) ])
          (same_length ps es q119)
          (conde
             [ q118 === !!false &&& (q114 === !!false)
             ; q118 === !!true &&& (q114 === q119)
             ])
          (conde
             [ fresh
                 pairs
                 (q114 === !!true)
                 (list_combine ps es pairs)
                 (list_all
                    (fun z q116 -> fresh (p e) (z === pair p e) (match1pat e p q116))
                    pairs
                    q109)
             ; q114 === !!false &&& (q109 === !!false)
             ]))
;;

let rec eval_pat s pats q104 =
  conde
    [ pats === nil () &&& (q104 === none ())
    ; fresh
        (p rhs ps q107)
        (pats === pair p rhs % ps)
        (match1pat s p q107)
        (conde
           [ q107 === !!true &&& (q104 === some rhs)
           ; q107 === !!false &&& eval_pat s ps q104
           ])
    ]
;;

let rec eval_pat_hacky s on_fail pats q103 =
  let rec helper acc pats q92 =
    conde
      [ pats === nil () &&& (on_fail === q92)
      ; fresh
          (p rhs ps q95)
          (pats === pair p rhs % ps)
          (match1pat s p q95)
          (conde
             [ fresh
                 q97
                 (q95 === !!true)
                 (q97 === !!true)
                 (rhs === q92)
                 (list_all
                    (fun p q100 ->
                      fresh
                        q99
                        (match1pat s p q99)
                        (conde
                           [ q99 === !!true &&& (q100 === !!false)
                           ; q99 === !!false &&& (q100 === !!true)
                           ]))
                    acc
                    q97)
             ; q95 === !!false &&& helper (p % acc) ps q92
             ])
      ]
  in
  helper (nil ()) pats q103
;;

let tinfo_names tt q91 = fresh xs (tt === t xs) (list_map fst xs q91)

let tinfo_names_with_arity tt q85 =
  fresh
    xs
    (tt === t xs)
    (list_map
       (fun p q88 ->
         fresh
           (q86 q87 q89)
           (q88 === pair q86 q87)
           (fst p q86)
           (snd p q89)
           (list_length q89 q87))
       xs
       q85)
;;

let tinfo_args tt name q84 = fresh xs (tt === t xs) (list_assoc name xs q84)
let tinfo_nth_arg tt n q83 = fresh xs (tt === t xs) (list_nth_nat n xs q83)
let info_assoc tt name q82 = fresh xs (tt === t xs) (list_assoc name xs q82)

let rec well_typed_expr e0 typs0 q78 =
  fresh
    (q79 tag es ts arg_infos)
    (q79 === pair e0 typs0)
    (q79 === pair (eConstr tag es) ts)
    (info_assoc typs0 tag arg_infos)
    (debug_lino __FILE__ __LINE__)
    (list_all2 well_typed_expr es arg_infos q78)
;;

let rec height_of_matchable root q73 =
  root
  === scru ()
  &&& (q73 === s (z ()))
  ||| fresh
        (q75 ss q76)
        (root === field q75 ss)
        (q73 === s q76)
        (debug_lino __FILE__ __LINE__)
        (height_of_matchable ss q76)
;;

let matchable_leq_nat m n q72 =
  let rec helper root q64 =
    conde
      [ root === pair (scru ()) (z ()) &&& (q64 === !!false)
      ; fresh q66 (root === pair (scru ()) (s q66)) (q64 === !!true)
      ; fresh
          (q68 m1 n1)
          (root === pair (field q68 m1) (s n1))
          (debug_lino __FILE__ __LINE__)
          (helper (pair m1 n1) q64)
      ; fresh (q69 q70) (root === pair (field q69 q70) (z ())) (q64 === !!false)
      ]
  in
  helper (pair m n) q72
;;

let rec eval_m s typinfo0 path0 q63 =
  let rec helper path q51 =
    conde
      [ path === scru () &&& (q51 === pair s typinfo0)
      ; fresh
          (nth scru q54 cname es next_tinfos arg_info q56 q57)
          (path === field nth scru)
          (q54 === pair (eConstr cname es) next_tinfos)
          (q51 === pair q56 q57)
          (debug_lino __FILE__ __LINE__)
          (helper scru q54)
          (info_assoc next_tinfos cname arg_info)
          (list_nth_nat nth es q56)
          (list_nth_nat nth arg_info q57)
      ]
  in
  fresh
    (q60 ans info q61)
    (q60 === pair ans info)
    (q63 === pair ans q61)
    (helper path0 q60)
    (tinfo_names_with_arity info q61)
;;

let rec not_in_history x xs q43 =
  conde
    [ xs === nil () &&& (q43 === !!true)
    ; fresh
        (h tl q46)
        (xs === h % tl)
        (conde [ x === h &&& (q46 === !!true); q46 === !!false &&& (x =/= h) ])
        (q46
        === !!false
        &&& not_in_history x tl q43
        ||| (q46 === !!true &&& (q43 === !!false)))
    ]
;;

let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_apply_domain ir q42 =
  let indeed_good_arity tinfo etag eargs q0 =
    fresh
      (sz q2 q4)
      (q2 === !!true)
      (q0 === !!true)
      (list_assoc etag tinfo sz)
      (conde [ q4 === sz &&& (q2 === !!true); q2 === !!false &&& (q4 =/= sz) ])
      (list_length eargs q4)
  in
  let rec inner history test_list irrr q9 =
    fresh
      ()
      (* (debug_var irrr (flip IR.reify) (function
          | [ ir ] ->
            Format.printf "inside inner: %s\n%!" (IR.show_logic ir);
            success
          | _ -> assert false)) *)
      (conde
         [ irrr === fail () &&& (q9 === none ())
         ; fresh n (irrr === lit n) (q9 === some n)
         ; fresh
             (m cases on_default q13 q15 etag eargs cnames q17 q19 q20)
             (irrr === switch m cases on_default)
             (q13 === !!true)
             (q15 === pair (eConstr etag eargs) cnames)
             (q17 === !!true)
             (q19 === !!true)
             (shortcut0 m max_height cases q13)
             (eval_m s tinfo m q15)
             (indeed_good_arity cnames etag eargs q17)
             (shortcut1 etag m cases history tinfo q19)
             (list_map fst cnames q20)
             (test_list (m % history) etag q20 on_default cases q9)
         ])
  in
  let rec test_list next_histo etag cnames on_default cases0 q39 =
    let rec helper constr_names cases q22 =
      fresh
        ()
        (* (debug_var
           constr_names
           (flip @@ Std.List.reify OCanren.reify)
           (function
             | _ ->
               Format.printf "%s %d\n%!" __FILE__ __LINE__;
               success)) *)
        (shortcut_apply_domain etag cnames !!true)
        (conde
           [ cases === nil () &&& inner next_histo test_list on_default q22
           ; fresh
               (constr_hd constr_tl qtag ontag clauses_tl q27)
               (cases =/= nil ())
               (constr_names === constr_hd % constr_tl)
               (cases === pair qtag ontag % clauses_tl)
               (conde
                  [ fresh
                      ()
                      (qtag === constr_hd)
                      (conde
                         [ qtag === etag &&& inner next_histo test_list ontag q22
                         ; qtag
                           =/= etag
                           &&& FD.neq qtag etag
                           &&& helper constr_tl clauses_tl q22
                         ])
                  ; qtag
                    =/= constr_hd
                    &&& (q27 === !!false)
                    &&& helper constr_tl cases q22
                  ])
           ])
    in
    helper cnames cases0 q39
  in
  inner (nil ()) test_list ir q42
;;
