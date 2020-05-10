open GT
open OCanren
open OCanren.Std
type 'a0 gnat =
  | Z
  | S of 'a0
module For_gnat = (Fmap)(struct let rec fmap fa0 = function | Z -> Z | S a0 -> S (fa0 a0)
                                type 'a0 t = 'a0 gnat end)
let rec z () = inj (For_gnat.distrib Z)
and s x__0 = inj (For_gnat.distrib (S x__0))
let nat_lt a b q218 =
  let rec helper root q213 =
    conde
      [fresh (q214) (root === (pair q214 (z ()))) (q213 === (!! false));
      fresh (q216) (root === (pair (z ()) (s q216))) (q213 === (!! true));
      fresh (x y) (root === (pair (s x) (s y))) (helper (pair x y) q213)] in
  helper (pair a b) q218
let nat_leq a b q212 =
  let rec helper root q207 =
    conde
      [fresh (q208) (root === (pair (z ()) q208)) (q207 === (!! true));
      fresh (q210) (root === (pair (s q210) (z ()))) (q207 === (!! false));
      fresh (x y) (root === (pair (s x) (s y))) (helper (pair x y) q207)] in
  helper (pair a b) q212
let fst z q204 = fresh (a q205) (z === (pair a q205)) (a === q204)
let rec list_mem x xs q196 =
  ((xs === (nil ())) &&& (q196 === (!! false))) |||
    (fresh (h tl q199) (xs === (h % tl)) (conde [(x === h) &&& (q199 === (!! true)); (q199 === (!! false)) &&& (x =/= h)])
       (conde [(q199 === (!! true)) &&& (q196 === (!! true)); (q199 === (!! false)) &&& (list_mem x tl q196)]))
let rec list_assoc name ys q189 =
  fresh (k v xs q191) (ys === ((pair k v) % xs)) (conde [(k === name) &&& (q191 === (!! true)); (q191 === (!! false)) &&& (k =/= name)])
    (conde [(q191 === (!! true)) &&& (v === q189); (q191 === (!! false)) &&& (list_assoc name xs q189)])
let list_map_all f =
  let rec helper xs q183 =
    ((xs === (nil ())) &&& (q183 === (!! true))) |||
      (fresh (y ys q186) (xs === (y % ys)) (f y q186) ((fresh (q187) (q186 === (some q187)) (helper xs q183)) ||| ((q186 === (none ())) &&& (q183 === (!! false))))) in
  helper
let list_map f xs q182 =
  let rec helper xs q176 = ((xs === (nil ())) &&& (q176 === (nil ()))) ||| (fresh (x q178 q179 q180) (xs === (x % q178)) (q176 === (q179 % q180)) (f x q179) (helper q178 q180)) in
  helper xs q182
let list_mapi f xs q175 =
  let rec helper i xs q169 =
    ((xs === (nil ())) &&& (q169 === (nil ()))) ||| (fresh (x q171 q172 q173) (xs === (x % q171)) (q169 === (q172 % q173)) (f i x q172) (helper (s i) q171 q173)) in
  helper (z ()) xs q175
let rec list_all f xs q163 =
  ((xs === (nil ())) &&& (q163 === (!! true))) |||
    (fresh (x q165 q167) (xs === (x % q165)) (f x q167) (conde [(q167 === (!! true)) &&& (list_all f q165 q163); (q167 === (!! false)) &&& (q163 === (!! false))]))
let rec same_length xs ys q151 =
  fresh (q152) (q152 === (pair xs ys))
    (conde
       [fresh (q153 xs q154 ys) (q152 === (pair (q153 % xs) (q154 % ys))) (same_length xs ys q151);
       fresh (q155 q156) (q152 === (pair (nil ()) (q155 % q156))) (q151 === (!! false));
       fresh (q158 q159) (q152 === (pair (q158 % q159) (nil ()))) (q151 === (!! false));
       (q152 === (pair (nil ()) (nil ()))) &&& (q151 === (!! true))])
let rec list_combine xs ys q145 =
  fresh (q146) (q146 === (pair xs ys))
    (((q146 === (pair (nil ()) (nil ()))) &&& (q145 === (nil ()))) |||
       (fresh (x xs y ys q148) (q146 === (pair (x % xs) (y % ys))) (q145 === ((pair x y) % q148)) (list_combine xs ys q148)))
let rec list_foldl f acc ys q141 = ((ys === (nil ())) &&& (acc === q141)) ||| (fresh (x xs q143) (ys === (x % xs)) (f acc x q143) (list_foldl f q143 xs q141))
let list_decorate_nat xs q139 = fresh (q138) (list_mapi (fun i -> fun x -> fun q140 -> i === q140) xs q138) (list_combine q138 xs q139)
let rec list_nth_nat idx xs q132 =
  fresh (q133) (q133 === (pair idx xs))
    ((fresh (x q134) (q133 === (pair (z ()) (x % q134))) (x === q132)) ||| (fresh (n q136 xs) (q133 === (pair (s n) (q136 % xs))) (list_nth_nat n xs q132)))
type ('a1, 'a0) gpattern =
  | WildCard
  | PConstr of 'a1 * 'a0
module For_gpattern =
  (Fmap2)(struct let rec fmap fa1 fa0 = function | WildCard -> WildCard | PConstr (a1_0, a0_1) -> PConstr ((fa1 a1_0), (fa0 a0_1))
                 type ('a1, 'a0) t = ('a1, 'a0) gpattern end)
let rec wildCard () = inj (For_gpattern.distrib WildCard)
and pConstr x__0 x__1 = inj (For_gpattern.distrib (PConstr (x__0, x__1)))
type ('a1, 'a0) gexpr =
  | EConstr of 'a1 * 'a0
module For_gexpr = (Fmap2)(struct let rec fmap fa1 fa0 = function | EConstr (a1_0, a0_1) -> EConstr ((fa1 a1_0), (fa0 a0_1))
                                  type ('a1, 'a0) t = ('a1, 'a0) gexpr end)
let rec eConstr x__0 x__1 = inj (For_gexpr.distrib (EConstr (x__0, x__1)))
let rec match1pat s p q113 =
  fresh (q114) (q114 === (pair s p))
    ((fresh (q115) (q114 === (pair q115 (wildCard ()))) (q113 === (!! true))) |||
       (fresh (tag1 es tag2 ps q118 q122 q123) (q114 === (pair (eConstr tag1 es) (pConstr tag2 ps)))
          (conde [(tag1 === tag2) &&& (q122 === (!! true)); (q122 === (!! false)) &&& (tag1 =/= tag2)]) (
          same_length ps es q123) (conde [(q122 === (!! false)) &&& (q118 === (!! false)); (q122 === (!! true)) &&& (q118 === q123)])
          (conde
             [fresh (pairs) (q118 === (!! true)) (list_combine ps es pairs) (list_all (fun z -> fun q120 -> fresh (p e) (z === (pair p e)) (match1pat e p q120)) pairs q113);
             (q118 === (!! false)) &&& (q113 === (!! false))])))
let rec eval_pat s pats q108 =
  ((pats === (nil ())) &&& (q108 === (none ()))) |||
    (fresh (p rhs ps q111) (pats === ((pair p rhs) % ps)) (match1pat s p q111)
       (conde [(q111 === (!! true)) &&& (q108 === (some rhs)); (q111 === (!! false)) &&& (eval_pat s ps q108)]))
let rec eval_pat_hacky s on_fail pats q107 =
  let rec helper acc pats q96 =
    ((pats === (nil ())) &&& (on_fail === q96)) |||
      (fresh (p rhs ps q99) (pats === ((pair p rhs) % ps)) (match1pat s p q99)
         (conde
            [fresh (q101) (q99 === (!! true)) (q101 === (!! true)) (rhs === q96)
               (list_all
                  (fun p -> fun q104 -> fresh (q103) (match1pat s p q103) (conde [(q103 === (!! true)) &&& (q104 === (!! false)); (q103 === (!! false)) &&& (q104 === (!! true))]))
                  acc q101);
            (q99 === (!! false)) &&& (helper (p % acc) ps q96)])) in
  helper (nil ()) pats q107
type ('a1, 'a0) gmatchable =
  | Scru
  | Field of 'a1 * 'a0
module For_gmatchable =
  (Fmap2)(struct let rec fmap fa1 fa0 = function | Scru -> Scru | Field (a1_0, a0_1) -> Field ((fa1 a1_0), (fa0 a0_1))
                 type ('a1, 'a0) t = ('a1, 'a0) gmatchable end)
let rec scru () = inj (For_gmatchable.distrib Scru)
and field x__0 x__1 = inj (For_gmatchable.distrib (Field (x__0, x__1)))
type ('a3, 'a2, 'a1, 'a0) gir =
  | Fail
  | Switch of 'a3 * 'a2 * 'a1
  | Lit of 'a0
module For_gir =
  (Fmap4)(struct
            let rec fmap fa3 fa2 fa1 fa0 = function | Fail -> Fail | Switch (a3_0, a2_1, a1_2) -> Switch ((fa3 a3_0), (fa2 a2_1), (fa1 a1_2)) | Lit a0 -> Lit (fa0 a0)
            type ('a3, 'a2, 'a1, 'a0) t = ('a3, 'a2, 'a1, 'a0) gir
          end)
let rec fail () = inj (For_gir.distrib Fail)
and switch x__0 x__1 x__2 = inj (For_gir.distrib (Switch (x__0, x__1, x__2)))
and lit x__0 = inj (For_gir.distrib (Lit x__0))
type 'a0 gtyp_info =
  | T of 'a0
module For_gtyp_info = (Fmap)(struct let rec fmap fa0 = function | T a0 -> T (fa0 a0)
                                     type 'a0 t = 'a0 gtyp_info end)
let rec t x__0 = inj (For_gtyp_info.distrib (T x__0))
let rec height_of_matchable root q91 =
  ((root === (scru ())) &&& (q91 === (s (z ())))) ||| (fresh (q93 ss q94) (root === (field q93 ss)) (q91 === (s q94)) (height_of_matchable ss q94))
let matchable_leq_nat m n q90 =
  let rec helper root q82 =
    conde
      [(root === (pair (scru ()) (z ()))) &&& (q82 === (!! false));
      fresh (q84) (root === (pair (scru ()) (s q84))) (q82 === (!! true));
      fresh (q86 m1 n1) (root === (pair (field q86 m1) (s n1))) (helper (pair m1 n1) q82);
      fresh (q87 q88) (root === (pair (field q87 q88) (z ()))) (q82 === (!! false))] in
  helper (pair m n) q90
let compile_naively pats q81 =
  let rec helper_pat scru pat rhs else_top q72 =
    fresh (tag args dec_args else_) (pat === (eConstr tag args)) (q72 === (switch scru ((pair tag rhs) % (nil ())) else_)) (
      list_decorate_nat args dec_args)
      (list_foldl (fun acc -> fun z -> fun q74 -> fresh (idx pat1) (z === (pair idx pat1)) (helper_pat (field idx scru) pat1 acc else_top q74)) rhs dec_args else_) in
  let rec helper pats q77 =
    ((pats === (nil ())) &&& (q77 === (fail ()))) ||| (fresh (p rhs ps else_) (pats === ((pair p rhs) % ps)) (helper ps else_) (helper_pat (scru ()) p rhs else_ q77)) in
  helper pats q81
let tinfo_names tt q71 = fresh (xs) (tt === (t xs)) (list_map fst xs q71)
let tinfo_args tt name q70 = fresh (xs) (tt === (t xs)) (list_assoc name xs q70)
let tinfo_nth_arg tt n q69 = fresh (xs) (tt === (t xs)) (list_nth_nat n xs q69)
let info_assoc tt name q68 = fresh (xs) (tt === (t xs)) (list_assoc name xs q68)
let rec eval_m s typinfo0 path0 q67 =
  let rec helper path q55 =
    ((path === (scru ())) &&& (q55 === (pair s typinfo0))) |||
      (fresh (nth scru q58 cname es next_tinfos arg_info q60 q61) (path === (field nth scru)) (
         q58 === (pair (eConstr cname es) next_tinfos)) (q55 === (pair q60 q61)) (
         helper scru q58) (info_assoc next_tinfos cname arg_info) (list_nth_nat nth es q60) (
         list_nth_nat nth arg_info q61)) in
  fresh (q64 ans info q65) (q64 === (pair ans info)) (q67 === (pair ans q65)) (helper path0 q64) (tinfo_names info q65)
let compile_naively pats q54 =
  let rec helper_pat scru pat rhs else_top q44 =
    ((pat === (wildCard ())) &&& (rhs === q44)) |||
      (fresh (tag args dec_args then_) (pat === (pConstr tag args)) (
         q44 === (switch scru ((pair tag then_) % (nil ())) else_top)) (
         list_decorate_nat args dec_args)
         (list_foldl (fun acc -> fun z -> fun q47 -> fresh (idx pat1) (z === (pair idx pat1)) (helper_pat (field idx scru) pat1 acc else_top q47)) rhs dec_args then_)) in
  let rec helper pats q50 =
    ((pats === (nil ())) &&& (q50 === (fail ()))) ||| (fresh (p rhs ps else_) (pats === ((pair p rhs) % ps)) (helper ps else_) (helper_pat (scru ()) p rhs else_ q50)) in
  helper pats q54
let rec not_in_history x xs q36 =
  ((xs === (nil ())) &&& (q36 === (!! true))) |||
    (fresh (h tl q39) (xs === (h % tl)) (conde [(x === h) &&& (q39 === (!! true)); (q39 === (!! false)) &&& (x =/= h)])
       (((q39 === (!! false)) &&& (not_in_history x tl q36)) ||| ((q39 === (!! true)) &&& (q36 === (!! false)))))

let rec eval_ir s max_height tinfo shortcut1 shortcut_tag ir q35 =
  let rec inner history test_list irrr q0 =
    conde
      [ (irrr === (fail ())) &&& (q0 === (none ()))
      ; fresh (n)
          (irrr === (lit n))
          (q0 === (some n))
      ; fresh (m cases on_default q8 etag args cnames)
        (irrr === (switch m cases on_default))
        (cases =/= nil())
        (q8 === (pair (eConstr etag args) cnames))
        (matchable_leq_nat m max_height !!true)

       (*(conde
          [ (cases === (nil ())) &&& (q6 === (!! true))
          ; (q6 === (!! false)) &&& (cases =/= (nil ()))])*)

        (eval_m s tinfo m q8)
        (shortcut1 etag m cases history !!true)
        (test_list (m % history) etag cnames on_default cases q0)
      ] in
  let rec test_list next_histo etag cnames on_default cases0 q33 =
    let rec helper constr_names cases q14 =

        conde
          [ (cases === (nil ())) &&& (inner next_histo test_list on_default q14)
          ; fresh (constr_hd constr_tl qtag ontag clauses_tl)
              (cases =/= (nil ()))

              (shortcut_tag constr_names cases !!true)
              (constr_names === (constr_hd % constr_tl))
              (cases === ((pair qtag ontag) % clauses_tl))

              (conde
                [ fresh (q23)
                    (qtag === constr_hd)
                    (conde
                       [ (qtag === etag) &&& (inner next_histo test_list ontag q14)
                       ; (qtag =/= etag) &&& (helper constr_tl clauses_tl q14)
                       ])
                ; (qtag =/= constr_hd) &&& (helper constr_tl cases q14)
                ])
           ]
    in
    helper cnames cases0 q33 in
  inner (nil ()) test_list ir q35
