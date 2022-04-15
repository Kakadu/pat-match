open OCanren
open OCanren.Std
open Work_base_common
open Unn_pre

let debug_int text v =
  debug_var v OCanren.reify (fun xs ->
      Format.printf "%s " text;
      Stdlib.List.iter
        (fun x ->
          Format.printf "%s " (GT.show OCanren.logic (GT.show GT.int) x))
        xs;
      Format.printf "\n%!";
      success)

let nat_lt a b q235 =
  let rec helper root q230 =
    conde
      [
        fresh q231 (root === pair q231 (z ())) (q230 === !!false);
        fresh q233 (root === pair (z ()) (s q233)) (q230 === !!true);
        fresh (x y) (root === pair (s x) (s y)) (helper (pair x y) q230);
      ]
  in
  helper (pair a b) q235

let nat_leq a b q229 =
  let rec helper root q224 =
    conde
      [
        fresh q225 (root === pair (z ()) q225) (q224 === !!true);
        fresh q227 (root === pair (s q227) (z ())) (q224 === !!false);
        fresh (x y)
          (root === pair (s x) (s y))
          (debug_lino __FILE__ __LINE__)
          (helper (pair x y) q224);
      ]
  in
  helper (pair a b) q229

let fst z q221 = fresh (a q222) (z === pair a q222) (a === q221)
let snd z q218 = fresh (q219 a) (z === pair q219 a) (a === q218)

let rec list_mem x xs q210 =
  conde
    [
      xs === nil () &&& (q210 === !!false);
      fresh (h tl)
        (debug_lino __FILE__ __LINE__)
        (xs === h % tl)
        (conde
           [ x === h &&& (q210 === !!true); x =/= h &&& list_mem x tl q210 ]);
    ]

let rec list_assoc name ys q203 =
  fresh (k v xs q205)
    (ys === pair k v % xs)
    (conde
       [ k === name &&& (q205 === !!true); q205 === !!false &&& (k =/= name) ])
    (conde
       [
         q205 === !!true &&& (v === q203);
         q205 === !!false &&& list_assoc name xs q203;
       ])

let list_map_all f =
  let rec helper xs q197 =
    conde
      [
        xs === nil () &&& (q197 === !!true);
        fresh (y ys q200)
          (xs === y % ys)
          (f y q200)
          (conde
             [
               fresh q201
                 (q200 === some q201)
                 (* (debug_lino __FILE__ __LINE__) *)
                 (helper xs q197);
               q200 === none () &&& (q197 === !!false);
             ]);
      ]
  in
  helper

let list_map f xs q196 =
  let rec helper xs q190 =
    conde
      [
        xs === nil () &&& (q190 === nil ());
        fresh (x q192 q193 q194)
          (xs === x % q192)
          (q190 === q193 % q194)
          (f x q193)
          (* (debug_lino __FILE__ __LINE__) *)
          (helper q192 q194);
      ]
  in
  helper xs q196

let list_mapi f xs q189 =
  let rec helper i xs q183 =
    conde
      [
        xs === nil () &&& (q183 === nil ());
        fresh (x q185 q186 q187)
          (xs === x % q185)
          (q183 === q186 % q187)
          (f i x q186)
          (* (debug_lino __FILE__ __LINE__) *)
          (helper (s i) q185 q187);
      ]
  in
  helper (z ()) xs q189

let rec list_all f xs q177 =
  conde
    [
      xs === nil () &&& (q177 === !!true);
      fresh (x q179 q181)
        (xs === x % q179)
        (f x q181)
        (conde
           [
             q181 === !!true
             &&& (* debug_lino __FILE__ __LINE__ &&&  *)
             list_all f q179 q177;
             q181 === !!false &&& (q177 === !!false);
           ]);
    ]

let rec list_all2 f xs0 ys0 q164 =
  fresh q165
    (q165 === pair xs0 ys0)
    (conde
       [
         fresh (x xs y ys q167)
           (q165 === pair (x % xs) (y % ys))
           (f x y q167)
           (conde
              [
                q167 === !!true
                &&& debug_lino __FILE__ __LINE__
                &&& list_all2 f xs ys q164;
                q167 === !!false &&& (q164 === !!false);
              ]);
         q165 === pair (nil ()) (nil ()) &&& (q164 === !!true);
         fresh (q170 q171)
           (q165 === pair (q170 % q171) (nil ()))
           (q164 === !!false);
         fresh (q173 q174)
           (q165 === pair (nil ()) (q173 % q174))
           (q164 === !!false);
       ])

let rec same_length xs ys q152 =
  fresh q153
    (q153 === pair xs ys)
    (conde
       [
         fresh (q154 xs q155 ys)
           (q153 === pair (q154 % xs) (q155 % ys))
           (debug_lino __FILE__ __LINE__)
           (same_length xs ys q152);
         fresh (q156 q157)
           (q153 === pair (nil ()) (q156 % q157))
           (q152 === !!false);
         fresh (q159 q160)
           (q153 === pair (q159 % q160) (nil ()))
           (q152 === !!false);
         q153 === pair (nil ()) (nil ()) &&& (q152 === !!true);
       ])

let rec list_combine xs ys q146 =
  fresh q147
    (q147 === pair xs ys)
    (conde
       [
         q147 === pair (nil ()) (nil ()) &&& (q146 === nil ());
         fresh (x xs y ys q149)
           (q147 === pair (x % xs) (y % ys))
           (q146 === pair x y % q149)
           (debug_lino __FILE__ __LINE__)
           (list_combine xs ys q149);
       ])

let rec list_itero f xs =
  conde
    [
      (* debug "list_itero: nil: start"
         &&& (xs === nil ())
         &&& debug "list_itero: nil: end"; *)
      xs === nil ();
      fresh (h tl)
        (* (debug "list_itero: cons: start") *)
        (xs === h % tl)
        (f h)
        (list_itero f tl) (* (debug "list_itero: cons: end") *)
        success;
    ]

let rec list_foldl f acc ys q142 =
  conde
    [
      ys === nil () &&& (acc === q142);
      fresh (x xs q144)
        (ys === x % xs)
        (f acc x q144)
        (* (debug_lino __FILE__ __LINE__) *)
        (list_foldl f q144 xs q142);
    ]

let list_decorate_nat xs q140 =
  fresh q139
    (list_mapi (fun i _x q141 -> i === q141) xs q139)
    (list_combine q139 xs q140)

let rec list_nth_nat idx xs q133 =
  conde
    [
      fresh q135 (idx === z ()) (xs === q133 % q135);
      fresh (n q137 tl)
        (idx === s n)
        (xs === q137 % tl)
        (list_nth_nat n tl q133);
    ]

let rec list_length xs rez =
  conde
    [
      xs === nil () &&& (rez === z ());
      fresh (q130 tl q131)
        (xs === q130 % tl)
        (rez === s q131)
        (list_length tl q131);
    ]

let rec match1pat s p q127 =
  fresh q128
    (q128 === pair s p)
    (fresh q129 (q128 === pair q129 (wildCard ())) (q127 === !!true)
    ||| fresh
          (tag1 es tag2 ps q132 q136 q137)
          (q128 === pair (eConstr tag1 es) (pConstr tag2 ps))
          (conde
             [
               tag1 === tag2 &&& (q136 === !!true);
               q136 === !!false &&& (tag1 =/= tag2) &&& FD.neq tag1 tag2;
             ])
          (same_length ps es q137)
          (conde
             [
               q136 === !!false &&& (q132 === !!false);
               q136 === !!true &&& (q132 === q137);
             ])
          (conde
             [
               fresh pairs (q132 === !!true) (list_combine ps es pairs)
                 (list_all
                    (fun z q134 ->
                      fresh (p e) (z === pair p e) (match1pat e p q134))
                    pairs q127);
               q132 === !!false &&& (q127 === !!false);
             ]))

let rec eval_pat s pats q104 =
  conde
    [
      pats === nil () &&& (q104 === none ());
      fresh (p rhs ps q107)
        (pats === pair p rhs % ps)
        (match1pat s p q107)
        (conde
           [
             q107 === !!true &&& (q104 === some rhs);
             q107 === !!false &&& eval_pat s ps q104;
           ]);
    ]

let rec eval_pat_hacky s on_fail pats q121 =
  let rec helper acc pats q110 =
    pats === nil () &&& (on_fail === q110)
    ||| fresh (p rhs ps q113)
          (pats === pair p rhs % ps)
          (match1pat s p q113)
          (conde
             [
               fresh q115 (q113 === !!true) (q115 === !!true) (rhs === q110)
                 (list_all
                    (fun p q118 ->
                      fresh q117 (match1pat s p q117)
                        (conde
                           [
                             q117 === !!true &&& (q118 === !!false);
                             q117 === !!false &&& (q118 === !!true);
                           ]))
                    acc q115);
               q113 === !!false &&& helper (p % acc) ps q110;
             ])
  in
  helper (nil ()) pats q121

let tinfo_names tt q109 = fresh xs (tt === t xs) (list_map fst xs q109)

let tinfo_names_with_arity tt q103 =
  fresh xs
    (tt === t xs)
    (list_map
       (fun p q106 ->
         fresh (q104 q105 q107)
           (q106 === pair q104 q105)
           (fst p q104) (snd p q107) (list_length q107 q105))
       xs q103)

let tinfo_args tt name q102 = fresh xs (tt === t xs) (list_assoc name xs q102)
let tinfo_nth_arg tt n q101 = fresh xs (tt === t xs) (list_nth_nat n xs q101)
let info_assoc tt name q100 = fresh xs (tt === t xs) (list_assoc name xs q100)

let rec well_typed_expr e0 typs0 q96 =
  fresh (q97 tag es ts arg_infos)
    (q97 === pair e0 typs0)
    (q97 === pair (eConstr tag es) ts)
    (info_assoc typs0 tag arg_infos)
    (list_all2 well_typed_expr es arg_infos q96)

let rec height_of_matchable root q91 =
  conde
    [
      root === scru () &&& (q91 === s (z ()));
      fresh (q93 ss q94)
        (root === field q93 ss)
        (q91 === s q94)
        (height_of_matchable ss q94);
    ]

let matchable_leq_nat m n q90 =
  let rec helper root q82 =
    conde
      [
        root === pair (scru ()) (z ()) &&& (q82 === !!false);
        fresh q84 (root === pair (scru ()) (s q84)) (q82 === !!true);
        fresh (q86 m1 n1)
          (root === pair (field q86 m1) (s n1))
          (helper (pair m1 n1) q82);
        fresh (q87 q88) (root === pair (field q87 q88) (z ())) (q82 === !!false);
      ]
  in
  helper (pair m n) q90

let rec eval_m (s : Expr.injected) (typinfo0 : Typs.injected)
    (path0 : Matchable.injected)
    (q81 :
      ( Expr.ground,
        _,
        (* list of pairs: name * arity *)
      (Tag.ground, N.ground) Pair.ground List.ground,
        _ )
      Std.Pair.groundi) =
  let rec helper path q69 =
    conde
      [
        path === scru () &&& (q69 === pair s typinfo0);
        fresh
          (nth scru q72 cname es next_tinfos arg_info q74 q75)
          (path === field nth scru)
          (q72 === pair (eConstr cname es) next_tinfos)
          (q69 === pair q74 q75)
          (helper scru q72)
          (info_assoc next_tinfos cname arg_info)
          (list_nth_nat nth es q74)
          (list_nth_nat nth arg_info q75);
      ]
  in
  fresh (sub_scru info q79)
    (helper path0 (pair sub_scru info))
    (tinfo_names_with_arity info q79)
    (q81 === pair sub_scru q79)

let rec not_in_history x xs q61 =
  conde
    [
      xs === nil () &&& (q61 === !!true);
      fresh (h tl q64)
        (xs === h % tl)
        (conde [ x === h &&& (q64 === !!true); q64 === !!false &&& (x =/= h) ])
        (conde
           [
             q64 === !!false &&& not_in_history x tl q61;
             q64 === !!true &&& (q61 === !!false);
           ]);
    ]

let minisleep (sec : float) =
  let _ = Unix.select [] [] [] sec in
  ()

open Format

let debug_helper reifier printer ?color text var =
  debug_var var reifier (fun xs ->
      let open Format in
      let () =
        (match color with
        | None -> printf "%s: %a\n%!" text
        | Some c -> printf "\027[%dm%s: %a\027[0m\n%!" c text)
          (pp_print_list printer) xs
      in
      minisleep 0.05;
      success)

let debug_name_arity_list =
  debug_helper
    (Std.List.reify (Std.Pair.reify Tag.reify N.reify))
    [%fmt: (Tag.logic, N.logic) Std.Pair.logic Std.List.logic]

let debug_tag_list text xs =
  debug_var xs (Std.List.reify OCanren.reify) (fun xs ->
      let open Format in
      Format.printf "%s: %a \n%!" text
        (pp_print_list [%fmt: GT.int OCanren.logic Std.List.logic])
        xs;
      minisleep 0.05;
      success)

let debug_ir ?color text xs =
  debug_var xs IR.reify (fun xs ->
      let open Format in
      Format.printf "%s: " text;
      let () =
        (match color with
        | None -> printf "%a\n%!"
        | Some c -> printf "\027[%dm%a\027[0m\n%!" c)
          (pp_print_list [%fmt: IR.logic])
          xs
      in
      minisleep 0.05;
      success)

let debug_peano text xs =
  debug_var xs Unn_pre.N.reify (fun xs ->
      let open Format in
      Format.printf "%s: " text;
      let () = printf "%a\n%!" (pp_print_list [%fmt: Unn_pre.N.logic]) xs in
      minisleep 0.05;
      success)

let debug_option_int ?color text xs =
  debug_var xs (Option.reify OCanren.reify) (fun xs ->
      let open Format in
      Format.printf "%s: " text;
      let () =
        (match color with
        | None -> printf "%a\n%!"
        | Some c -> printf "\027[%dm%a\027[0m\n%!" c)
          (pp_print_list [%fmt: GT.int OCanren.logic Std.Option.logic])
          xs
      in
      minisleep 0.05;
      success)

let debug_tag_pair text xs =
  debug_var xs (Std.Pair.reify Tag.reify Tag.reify) (fun xs ->
      let open Format in
      Format.printf "%s: %a \n%!" text
        (pp_print_list [%fmt: (Tag.logic, Tag.logic) Std.Pair.logic])
        xs;
      minisleep 0.05;
      success)

let debug_tag text xs =
  debug_var xs Tag.reify (fun xs ->
      let open Format in
      Format.printf "%s: %a \n%!" text (pp_print_list [%fmt: Tag.logic]) xs;
      minisleep 0.05;
      success)

let debug_expr text xs =
  debug_var xs Expr.reify (fun xs ->
      let open Format in
      Format.printf "%s: %a \n%!" text
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ") Expr.pp_logic)
        xs;
      minisleep 0.05;
      success)

let debug_matchable_kind text xs =
  debug_var xs MatchableKind.reify (fun xs ->
      let open Format in
      Format.printf "%s: %a \n%!" text (pp_print_list MatchableKind.pp_logic) xs;
      minisleep 0.05;
      success)

let debug_matchable text xs =
  debug_var xs Matchable.reify (fun xs ->
      let open Format in
      Format.printf "%s: %a \n%!" text
        (pp_print_list (GT.fmt Matchable.logic))
        xs;
      minisleep 0.05;
      success)

let debug_cases text xs =
  debug_var xs
    (List.reify (Pair.reify Tag.reify IR.reify))
    (fun xs ->
      let open Format in
      Format.printf "%s: \027[%dm%a\027[0m \n%!" text 35
        (pp_print_list
           [%fmt: (Tag.logic, IR.logic) Std.Pair.logic Std.List.logic])
        xs;
      minisleep 0.05;
      success)

let is_list_coercible_to_ground onarg xs =
  let rec helper = function
    | Var _ -> false
    | Value (Std.List.Cons (x, tl)) -> onarg x && helper tl
    | Value Std.List.Nil -> true
  in
  helper xs

let assert_list_tag_is_ground ts =
  let is_int_coercible_to_ground = function Value _ -> true | _ -> false in
  debug_var ts (List.reify Tag.reify) (function
    | [ tags ] ->
        if is_list_coercible_to_ground is_int_coercible_to_ground tags then
          success
        else failure
    | [] -> failwith "no available constructors"
    | _ -> assert false)

let dirty_hack branches ~f:myeval (rez : (int option, _) OCanren.injected) ir0 =
  let rec helper branches ~ok_branches =
    conde
      [
        fresh () (branches === Std.nil ()) (ok_branches === Std.nil ());
        fresh (btl btag brhs ans)
          (branches === Std.pair btag brhs % btl)
          (debug "  Testing a branch")
          (OCanren.Unique.unique_answers (myeval btag brhs) ans)
          (debug "  After unique_answers call")
          (conde
             [
               fresh (temp br_tl)
                 (* TODO: What to pass as expected answer? *)
                 (rez === Std.Option.some temp)
                 (ans === Unique.unique temp)
                 (debug_lino __FILE__ __LINE__)
                 (debug_int "unique: " temp)
                 (ok_branches === Std.pair btag brhs % br_tl)
                 (helper ~ok_branches:br_tl btl);
               fresh () (ans === Unique.noanswer)
                 (debug_lino __FILE__ __LINE__)
                 (rez === Std.Option.none ())
                 (helper ~ok_branches btl);
               fresh () (ans === Unique.different)
                 (debug_lino __FILE__ __LINE__)
                 failure;
             ]);
      ]
  in
  fresh ok_branches
    (debug_lino __FILE__ __LINE__)
    (helper branches ~ok_branches)
    (debug_option_int "rez looks like " rez)
    (conde
       [
         rez === Std.Option.none ();
         fresh (temp l)
           (rez === Std.Option.some temp)
           (debug_lino __FILE__ __LINE__)
           (is_free temp
              (debug "CUTTING EARLY" &&& failure)
              (fresh () (debug_int "HERRR" temp)
                 (list_length ok_branches l)
                 (debug_peano "ok_bbranches length = " l)
                 (list_itero
                    (fun br ->
                      fresh (btag brhs)
                        (br === Std.pair btag brhs)
                        (* (debug_ir "calling myeval on rhs = " brhs) *)
                        (myeval btag brhs temp)
                      (* (debug_ir "new rhs = " brhs) *))
                    ok_branches)));
       ])
    (debug_ir "Specialized result = " ir0)

(** Checks that first list is not longer than the second one. Relationally *)
let rec no_longer_than left right ans =
  conde
    [
      left === Std.nil () &&& (ans === !!true);
      fresh (hl tll hr tlr)
        (left === hl % tll)
        (conde
           [
             right === Std.nil () &&& (ans === !!false);
             right === hr % tlr &&& no_longer_than tll tlr ans;
           ]);
    ]

let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_apply_domain
    _shortcut_branch ir q60 =
  let indeed_good_arity tinfo etag eargs q0 =
    fresh (sz q2 q4) (q2 === !!true) (q0 === !!true) (list_assoc etag tinfo sz)
      (* Manual reorder here *)
      (conde [ q4 === sz &&& (q2 === !!true); q2 === !!false &&& (q4 =/= sz) ])
      (list_length eargs q4)
  in

  let union_cases_and_default ~cnames cases default_rhs new_cases =
    fresh default_tag
      (shortcut_apply_domain default_tag cnames !!true)
      (debug_cases "union_cases_and_default: cases = " cases)
      (list_itero
         (fun br ->
           fresh c (fst br c)
             (debug "Trying to add disequality")
             (debug_tag "c=" c)
             (debug_tag_pair "between tags: " (Std.pair default_tag c))
             trace_domain_constraints
             (debug_ir ~color:32 "current IR = " ir)
             (default_tag =/= c) (FD.neq default_tag c)
             (debug "Disequality added"))
         cases)
      (Std.List.appendo cases !<(Std.pair default_tag default_rhs) new_cases)
  in
  (* Function that takes a pattern matching and prepares it to interate over all branches.
     The default cases is promotes to be a last branch
  *)
  let rec inner history test_list irrr inner_rez =
    fresh ()
      (debug_option_int "inner_rez" inner_rez)
      (debug_ir "root ir = " ir)
      (debug_ir "irrrr   = " irrr)
      (conde
         [
           irrr === fail () &&& (inner_rez === none ());
           fresh_ n
             (debug_ir "unifying with literal" irrr)
             (irrr === lit n)
             (debug "done!")
             (inner_rez === some n)
             (debug_lino __FILE__ __LINE__)
             (debug_ir "root_ir" ir);
           fresh_
             (m cases on_default is_forbidden sub_scru typ_info etag eargs
                only_names new_cases)
             (irrr === switch m cases on_default)
             (debug_ir "ir =" irrr) (debug_expr "scru = " s)
             (eval_m s tinfo m (pair sub_scru typ_info))
             (sub_scru === eConstr etag eargs)
             (*
             (conde
                [
                  fresh (targs scru_eargs)
                    (tinfo === t !<(pair __ targs))
                    (s === Expr.constr __ scru_eargs)
                    (same_length targs scru_eargs !!true);
                  tinfo === t (Std.nil ());
                  tinfo === t (__ % (__ % __));
                ])
                *)
             (conde
                [
                  typ_info === Std.nil ();
                  fresh (_the_tag arity)
                    (typ_info === !<(pair _the_tag arity))
                    (* if only single constructor *)
                    (debug_expr "cutting off sub_scru" sub_scru)
                    (etag === _the_tag)
                    (* I'm not sure it is 100% correct but ... *)
                    (list_length eargs arity)
                    (debug_expr "after cutting off = " sub_scru);
                  fresh () (typ_info === __ % (__ % __));
                ])
             trace_diseq_constraints
             (* (debug_tag "sub_scru:etag 00000" etag) *)
             (shortcut0 m max_height cases is_forbidden)
             (* Next line fixes hangings *)
             (* (debug_tag_list "only_names = " only_names) *)
             (shortcut1 etag m cases history tinfo !!true)
             (list_map fst typ_info only_names)
             (shortcut_apply_domain etag only_names !!true)
             (* TODO: this line helps, but we probably forget about already created disequality constraints *)
             (* (eargs === Std.nil ()) *)
             (* Hack! *)
             (debug_tag "sub_scru:etag" etag)
             trace_domain_constraints trace_diseq_constraints
             (* (conde_no_int *)
             (* (conde
                [
                  fresh ()
                    (etag === !!(Tag.of_string_exn "true"))
                    (eargs === Std.nil ());
                  fresh ()
                    (etag === !!(Tag.of_string_exn "false"))
                    (eargs === Std.nil ())
                  (* ; fresh () (etag === !!(Tag.of_string_exn "pair")) *);
                ])
             *)
             (debug_expr "sub_scru" sub_scru)
             (union_cases_and_default cases on_default new_cases
                ~cnames:only_names)
             (no_longer_than new_cases only_names !!true)
             (debug_cases "new_cases" new_cases)
             (debug_tag_list "available tags here" only_names)
             (debug_matchable_kind "is_forbidden: init: " is_forbidden)
             (test_list
                ~shortcut_history:(fun () ->
                  (* TODO: maybe delay is not required *)
                  shortcut1 etag m cases history tinfo !!true)
                (m % history) ~etag ~eargs typ_info new_cases is_forbidden
                inner_rez)
             (debug_option_int "test_list finished. inner_rez = " inner_rez);
         ])
  in
  let rec test_list ~shortcut_history next_histo ~etag ~eargs typ_info cases0
      is_forbidden test_list_rez =
    let case_2 new_cases =
      fresh _final_int
        (debug (sprintf "  case_2: %s" __FILE__))
        (dirty_hack new_cases test_list_rez
           ~f:(fun tag rhs rrrr ->
             fresh ()
               (* (shortcut_apply_domain tag only_names !!true) *)
               (debug_tag_pair "myeval started: too many tags could be there"
                  (Std.pair tag etag))
               (debug_ir "rhs = " rhs) (debug_int "rrrr" rrrr)
               (* TODO: Maybe we should use unique_answers here to speedup everything *)
               (tag === etag)
               (shortcut_history ())
               (inner next_histo test_list rhs (Std.some rrrr))
               (debug_int "myeval: ENDED " rrrr))
           ir)
    in
    let rec iter_cnames br_tag name_arity_list sk =
      conde
        [
          name_arity_list === nil () &&& debug "bad program1" &&& failure;
          fresh
            (constr_hd arity constr_tl)
            (name_arity_list === Std.pair constr_hd arity % constr_tl)
            (conde
               [
                 constr_hd === br_tag &&& list_length eargs arity
                 &&& sk constr_tl;
                 constr_hd =/= br_tag &&& iter_cnames br_tag constr_tl sk;
               ]);
        ]
    in
    let rec cases_3_and_4 eta = helper eta
    and helper ~old_branches ~left_name_arity_list ~original_domain cases
        helper_rez =
      fresh ()
        (no_longer_than cases typ_info !!true)
        (debug_cases "left cases = " cases)
        (debug_name_arity_list "left_name_arity_list = " left_name_arity_list)
        (debug_name_arity_list "typ_info = " typ_info)
        (conde
           [
             cases === nil () &&& debug "bad program2" &&& failure;
             fresh (brtl tag rhs)
               (Stdlib.List.fold_left
                  (fun acc v ->
                    print_endline "added a new constraint on branch";
                    acc &&& (v =/= tag))
                  success old_branches)
               (cases === Std.pair tag rhs % brtl)
               (debug_tag "etag = " etag)
               (debug_tag "head branch containts" tag)
               trace_domain_constraints
               (debug_matchable_kind "is_forbidden" is_forbidden)
               (shortcut_apply_domain tag original_domain !!true)
               (debug_tag "head branch containts: after shortcut: " tag)
               (iter_cnames tag left_name_arity_list (fun left_typ_info ->
                    debug_tag "iter: tag = " tag
                    &&& debug_tag "iter: etag = " etag
                    &&& fresh branch_n
                          (conde
                             [
                               fresh () (branch_n === !!1) (etag === tag)
                                 (FD.eq etag tag) (debug "branch 1")
                                 (debug_tag "head branch containts" tag)
                                 (debug_tag "etag = " etag)
                                 (is_forbidden === goodSubTree ());
                               fresh () (branch_n === !!2) (etag === tag)
                                 (FD.eq etag tag) (debug "branch 2")
                                 (is_forbidden === missExample ());
                               fresh () (branch_n === !!3) (etag =/= tag)
                                 (FD.neq etag tag) (debug "branch 3")
                                 (is_forbidden === goodSubTree ());
                               fresh () (branch_n === !!4) (etag =/= tag)
                                 (FD.neq etag tag) (debug "branch 4")
                                 (is_forbidden === missExample ());
                             ])
                          (debug_int "branch_n = " branch_n)
                          (conde
                             [
                               fresh () (branch_n === !!1)
                                 (debug_lino "branch 1 hit" __LINE__)
                                 (inner next_histo test_list rhs helper_rez)
                                 (debug ">>> leaving branch 1 ");
                               fresh () (branch_n === !!2)
                                 (debug_lino "branch 2 hit!" __LINE__)
                                 (* (debug_tag_pair "branch 2 hit!" (Std.pair tag etag)) *)
                                 (* (debug_var etag Tag.reify (fun _ -> assert false)) *)
                                 (case_2 cases)
                                 (debug ">>> leaving branch 2 ");
                               fresh () (branch_n === !!3)
                                 (debug_lino __FILE__ __LINE__)
                                 (cases_3_and_4 ~original_domain
                                    ~old_branches:(tag :: old_branches)
                                    ~left_name_arity_list:left_typ_info brtl
                                    helper_rez);
                               fresh () (branch_n === !!4)
                                 (debug_lino "branch 4 hit!" __LINE__)
                                 (debug_lino __FILE__ __LINE__)
                                 (cases_3_and_4 ~original_domain
                                    ~old_branches:(tag :: old_branches)
                                    ~left_name_arity_list:left_typ_info brtl
                                    helper_rez)
                                 (debug ">>> leaving branch 4");
                             ])));
           ])
    in

    (* fresh () (debug "test_list called")
       (shortcut_apply_domain etag cnames !!true)
       (helper ~old_branches:[] cnames cases0 test_list_rez)
       (debug_option_int "test_list_rez" test_list_rez) *)
    fresh original_domain (debug "test_list called") (debug_tag "etag: " etag)
      (list_map fst typ_info original_domain)
      (no_longer_than cases0 typ_info !!true)
      (* &&& FD.domain etag [ 2; 3 ] *)
      (* &&& FD.neq etag !!2  *)
      trace_domain_constraints
      (shortcut_apply_domain etag original_domain !!true)
      (debug_cases "cases0 = " cases0)
      (helper ~old_branches:[] ~original_domain ~left_name_arity_list:typ_info
         cases0 test_list_rez)
      (debug_option_int "test_list_rez" test_list_rez)
  in
  inner (nil ()) test_list ir q60
