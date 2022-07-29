open OCanren
open OCanren.Std
open Pre

let rec list_assoc : _ =
 fun name ys q203 ->
  fresh (k v xs q205)
    (ys === pair k v % xs)
    (conde
       [ k === name &&& (q205 === !!true); q205 === !!false &&& (k =/= name) ])
    (conde
       [
         q205 === !!true &&& (v === q203);
         q205 === !!false &&& list_assoc name xs q203;
       ])

let info_assoc tt name q82 =
  fresh xs (tt === Pre.Typ_info.t xs) (list_assoc name xs q82)

let rec list_nth_nat :
    N.injected -> (N.injected, _) Std.Pair.injected Std.List.injected -> _ =
 fun idx xs rez ->
  fresh q134
    (q134 === pair idx xs)
    (conde
       [
         fresh (x q135) (q134 === pair Pre.N.z (x % q135)) (x === rez);
         fresh (n q137 xs)
           (q134 === pair (N.s n) (q137 % xs))
           (list_nth_nat n xs rez);
       ])

let rec eval_m :
    Expr.injected ->
    Typ_info.injected ->
    Matchable.injected ->
    sub_expr:Expr.injected ->
    sub_typ_info:Typ_info.injected ->
    goal =
 fun s typinfo0 path0 ~sub_expr ~sub_typ_info ->
  let rec helper path sub_expr sub_typ_info =
    conde
      [
        fresh ()
          (path === Matchable.scru ())
          (sub_expr === s)
          (sub_typ_info === typinfo0);
        fresh
          (nth scru q54 cname es next_tinfos arg_info q56 q57)
          (path === Matchable.field nth scru)
          (q54 === pair (Expr.eConstr cname es) next_tinfos)
          (q51 === pair q56 q57)
          (* (debug_lino __FILE__ __LINE__) *)
          (helper scru q54)
          (info_assoc next_tinfos cname arg_info)
          (list_nth_nat nth es q56)
          (list_nth_nat nth arg_info q57);
      ]
  in
  fresh (q60 ans info q61)
    (q60 === pair ans info)
    (q63 === pair ans q61)
    (helper path0 q60)
    (tinfo_names_with_arity info q61)

let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_apply_domain =
  let rec inner irrr rez =
    conde
      [
        fresh n (irrr === IR.lit n) (rez === Std.Option.some n);
        fresh () (irrr === IR.fail ()) (rez === Std.Option.none ());
        fresh
          (tag m br_th br_el sub_expr)
          (irrr === IR.ite tag m br_th br_el)
          (eval_m s tinfo m sub_expr);
      ]
  in

  fun ir rez -> inner ir rez
