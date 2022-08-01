open OCanren
open OCanren.Std
open Pre

let rec list_assoc : _ -> _ Std.List.injected -> _ -> goal =
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

let info_assoc :
    Typ_info.injected ->
    Tag.injected ->
    Typ_info.injected Std.List.injected ->
    goal =
 fun tt name q82 ->
  fresh xs (Pre.Typ_info.unwrap tt xs) (list_assoc name xs q82)

let rec list_nth_nat : N.injected -> 'el Std.List.injected -> 'el -> goal =
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
  let rec helper path current_expr (current_typinfo : Typ_info.injected) =
    conde
      [
        fresh ()
          (path === Matchable.scru ())
          (sub_expr === current_expr)
          (sub_typ_info === typinfo0);
        fresh
          (nth subpath constr_tag es sub_expr args_tinfo_list sub_typ_info temp)
          (path === Matchable.field nth subpath)
          (Typ_info.unwrap sub_typ_info temp)
          (current_expr === Expr.eConstr constr_tag es)
          (list_nth_nat nth es sub_expr)
          (info_assoc current_typinfo constr_tag args_tinfo_list)
          (list_nth_nat nth args_tinfo_list sub_typ_info)
          (helper subpath sub_expr sub_typ_info);
      ]
  in
  fresh () (helper path0 s typinfo0)

let rec not_in_history q xs =
  conde
    [
      xs === Std.nil ();
      fresh (h tl) (xs === h % tl) (h =/= q) (not_in_history q tl);
    ]

let extend_history new_m his new_his = new_his === new_m % his

let trace_history msg his =
  debug_var his (Std.List.reify Matchable.reify) (fun xs ->
      Format.printf "%s %a\n%!" msg
        [%fmt: Matchable.logic Std.List.logic GT.list] xs;
      success)

let rec eval_ir ?(add_domain = fun _ ~iftag:_ ~etag:_ ~eargs:_ -> success)
    ?(fd_domain_hint = fun _ _ _ -> success) s tinfo :
    IR.injected -> _ Std.Option.groundi -> goal =
  let rec inner ~history:old_history irrr rez =
    conde
      [
        fresh n (irrr === IR.lit n) (rez === Std.Option.some n);
        fresh () (irrr === IR.fail ()) (rez === Std.Option.none ());
        fresh
          (tag m br_th br_el history sub_expr sub_typ_info etag eargs)
          (irrr === IR.ite m tag br_th br_el)
          (sub_expr === Expr.eConstr etag eargs)
          (add_domain m ~iftag:tag ~etag ~eargs)
          (not_in_history m old_history)
          (extend_history m old_history history)
          (* (trace_history "history =" history) *)
          (eval_m s tinfo m ~sub_expr ~sub_typ_info)
          (fd_domain_hint m etag eargs)
          (conde
             [
               etag === tag &&& inner ~history br_th rez;
               etag =/= tag &&& FD.neq etag tag &&& inner ~history br_el rez;
             ]);
      ]
  in

  inner ~history:(Std.nil ())

let set_boolean_domain etag =
  FD.domain etag [ Tag.of_string_exn "true"; Tag.of_string_exn "false" ]

let run_ir eta =
  let open Tester in
  run_r IR.reify (GT.show IR.logic) eta

let tinfo_triple_of_bools =
  let bool =
    Typ_info.mkt
      [
        (Tag.of_string_exn "true", Std.List.of_list Fun.id []);
        (Tag.of_string_exn "false", Std.List.of_list Fun.id []);
      ]
  in
  Typ_info.mkt
    [
      (Tag.of_string_exn "triple", Std.List.of_list Fun.id [ bool; bool; bool ]);
    ]
  |> Typ_info.inject
