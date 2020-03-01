open GT
open OCanren
open OCanren.Std
let list_map_all f =
  let rec helper xs q91 =
    ((xs === (nil ())) &&& (q91 === (!! true))) |||
      (fresh (y ys q94) (xs === (y % ys)) (f y q94)
         ((fresh (q95) (q94 === (some q95)) (helper xs q91)) |||
            ((q94 === (none ())) &&& (q91 === (!! false))))) in
  helper
let rec list_all f xs q85 =
  ((xs === (nil ())) &&& (q85 === (!! true))) |||
    (fresh (x q87 q89) (xs === (x % q87)) (f x q89)
       (conde
          [(q89 === (!! true)) &&& (list_all f q87 q85);
          (q89 === (!! false)) &&& (q85 === (!! false))]))
let rec same_length xs ys q73 =
  fresh (q74) (q74 === (pair xs ys))
    (conde
       [fresh (q75 xs q76 ys) (q74 === (pair (q75 % xs) (q76 % ys)))
          (same_length xs ys q73);
       fresh (q77 q78) (q74 === (pair (nil ()) (q77 % q78)))
         (q73 === (!! false));
       fresh (q80 q81) (q74 === (pair (q80 % q81) (nil ())))
         (q73 === (!! false));
       (q74 === (pair (nil ()) (nil ()))) &&& (q73 === (!! true))])
let rec list_combine xs ys q67 =
  fresh (q68) (q68 === (pair xs ys))
    (((q68 === (pair (nil ()) (nil ()))) &&& (q67 === (nil ()))) |||
       (fresh (x xs y ys q70) (q68 === (pair (x % xs) (y % ys)))
          (q67 === ((pair x y) % q70)) (list_combine xs ys q70)))
type 'a0 gnat =
  | Z 
  | S of 'a0 
module For_gnat =
  (Fmap)(struct
           let rec fmap fa0 = function | Z -> Z | S a0 -> S (fa0 a0)
           type 'a0 t = 'a0 gnat
         end)
let rec z () = inj (For_gnat.distrib Z)
and s x__0 = inj (For_gnat.distrib (S x__0))

let rec list_nth_nat idx xs q61 =
  fresh (q62) (q62 === (pair idx xs))
    ((fresh (x q63) (q62 === (pair (z ()) (x % q63))) (x === q61)) |||
       (fresh (n q65 xs) (q62 === (pair (s n) (q65 % xs)))
          (list_nth_nat n xs q61)))

type ('a1, 'a0) gpattern =
  | WildCard 
  | PConstr of 'a1 * 'a0 
module For_gpattern =
  (Fmap2)(struct
            let rec fmap fa1 fa0 =
              function
              | WildCard -> WildCard
              | PConstr (a1_0, a0_1) -> PConstr ((fa1 a1_0), (fa0 a0_1))
            type ('a1, 'a0) t = ('a1, 'a0) gpattern
          end)
let rec wildCard () = inj (For_gpattern.distrib WildCard)
and pConstr x__0 x__1 = inj (For_gpattern.distrib (PConstr (x__0, x__1)))
type ('a1, 'a0) gexpr =
  | EConstr of 'a1 * 'a0 
module For_gexpr =
  (Fmap2)(struct
            let rec fmap fa1 fa0 =
              function
              | EConstr (a1_0, a0_1) -> EConstr ((fa1 a1_0), (fa0 a0_1))
            type ('a1, 'a0) t = ('a1, 'a0) gexpr
          end)
let rec eConstr x__0 x__1 = inj (For_gexpr.distrib (EConstr (x__0, x__1)))
let rec match1pat s p q42 =
  fresh (q43) (q43 === (pair s p))
    ((fresh (q44) (q43 === (pair q44 (wildCard ()))) (q42 === (!! true))) |||
       (fresh (tag1 es tag2 ps q47 q51 q52)
          (q43 === (pair (eConstr tag1 es) (pConstr tag2 ps)))
          (conde
             [(tag1 === tag2) &&& (q51 === (!! true));
             (q51 === (!! false)) &&& (tag1 =/= tag2)])
          (same_length ps es q52)
          (conde
             [(q51 === (!! false)) &&& (q47 === (!! false));
             (q51 === (!! true)) &&& (q47 === q52)])
          (conde
             [fresh (pairs) (q47 === (!! true)) (list_combine ps es pairs)
                (list_all
                   (fun z ->
                      fun q49 ->
                        fresh (p e) (z === (pair p e)) (match1pat e p q49))
                   pairs q42);
             (q47 === (!! false)) &&& (q42 === (!! false))])))
let rec eval_pat s pats q37 =
  ((pats === (nil ())) &&& (q37 === (none ()))) |||
    (fresh (p rhs ps q40) (pats === ((pair p rhs) % ps)) (match1pat s p q40)
       (conde
          [(q40 === (!! true)) &&& (q37 === (some rhs));
          (q40 === (!! false)) &&& (eval_pat s ps q37)]))
let rec eval_pat_hacky s on_fail pats q36 =
  let rec helper acc pats q25 =
    ((pats === (nil ())) &&& (on_fail === q25)) |||
      (fresh (p rhs ps q28) (pats === ((pair p rhs) % ps))
         (match1pat s p q28)
         (conde
            [fresh (q30) (q28 === (!! true)) (q30 === (!! true))
               (rhs === q25)
               (list_all
                  (fun p ->
                     fun q33 ->
                       fresh (q32) (match1pat s p q32)
                         (conde
                            [(q32 === (!! true)) &&& (q33 === (!! false));
                            (q32 === (!! false)) &&& (q33 === (!! true))]))
                  acc q30);
            (q28 === (!! false)) &&& (helper (p % acc) ps q25)])) in
  helper (nil ()) pats q36
type ('a1, 'a0) gmatchable =
  | Scru 
  | Field of 'a1 * 'a0 
module For_gmatchable =
  (Fmap2)(struct
            let rec fmap fa1 fa0 =
              function
              | Scru -> Scru
              | Field (a1_0, a0_1) -> Field ((fa1 a1_0), (fa0 a0_1))
            type ('a1, 'a0) t = ('a1, 'a0) gmatchable
          end)
let rec scru () = inj (For_gmatchable.distrib Scru)
and field x__0 x__1 = inj (For_gmatchable.distrib (Field (x__0, x__1)))
type ('a3, 'a2, 'a1, 'a0) gir =
  | Fail 
  | IFTag of 'a3 * 'a2 * 'a1 * 'a1 
  | Int of 'a0 
module For_gir =
  (Fmap4)(struct
            let rec fmap fa3 fa2 fa1 fa0 =
              function
              | Fail -> Fail
              | IFTag (a3_0, a2_1, a1_2, a1_3) ->
                  IFTag ((fa3 a3_0), (fa2 a2_1), (fa1 a1_2), (fa1 a1_3))
              | Int a0 -> Int (fa0 a0)
            type ('a3, 'a2, 'a1, 'a0) t = ('a3, 'a2, 'a1, 'a0) gir
          end)
let rec fail () = inj (For_gir.distrib Fail)
and iFTag x__0 x__1 x__2 x__3 =
  inj (For_gir.distrib (IFTag (x__0, x__1, x__2, x__3)))
and int x__0 = inj (For_gir.distrib (Int x__0))
let rec eval_m s h q20 =
  ((h === (scru ())) &&& (s === q20)) |||
    (fresh (n m q23 q24 es) (h === (field n m)) (q23 === (eConstr q24 es))
       (eval_m s m q23) (list_nth_nat n es q20))

let rec eval_ir s ir q10 =
  conde
    [ (ir === (fail ())) &&& (q10 === (none ()))
    ; fresh (n)
        (ir === (int n))
        (q10 === (some n))
    ; fresh (tag scru th el q14 tag2 args q16)
        (ir === (iFTag tag scru th el))
        (q14 === (eConstr tag2 args)) (eval_m s scru q14)
        (conde
           [ (tag2 === tag) &&& (q16 === (!! true))
           ; (q16 === (!! false)) &&& (tag2 =/= tag)
           ])
        (conde
           [ (q16 === (!! true)) &&& (eval_ir s th q10)
           ; (q16 === (!! false)) &&& (eval_ir s el q10)
           ])
    ]


(*
let rec eval_ir_hacky s ir q0 =
  conde
    [(ir === (fail ())) &&& (q0 === (fail ()));
    fresh (n) (ir === (int n)) (q0 === (int n));
    fresh (tag scru th el q4 tag2 args q6) (ir === (iFTag tag scru th el))
      (q4 === (eConstr tag2 args)) (eval_m s scru q4)
      (conde
         [(tag2 === tag) &&& (q6 === (!! true));
         (q6 === (!! false)) &&& (tag2 =/= tag)])
      (conde
         [(q6 === (!! true)) &&& (eval_ir_hacky s th q0);
         (q6 === (!! false)) &&& (eval_ir_hacky s el q0)])]
*)
