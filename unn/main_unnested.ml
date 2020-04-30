module Work = Work_unnested
open Printf
open Work
open OCanren
open Mytester
open Helper
open Unn_pre



let eleaf s = eConstr !!s @@ Std.List.nil ()
let epair a b = eConstr !!"pair" (Std.List.list [a;b])

let print_demos msg xs =
  Printf.printf "<%s>\n" msg;
  List.iter (fun p -> Printf.printf "\t\t%s\n" (Expr.show p)) xs;
  Printf.printf "</%s>\n" msg





(*


  let run_hacky ?(n=10) clauses  =
    let injected_pats = Clauses.inject clauses in

    let injected_exprs =
      let demo_exprs =
        let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
        let prjl e =
          Std.List.prjc
            prj1
            (fun _ _ -> failwith "should not happen2")
            e
          in
        let prjp e =
          Std.Pair.prjc
            prjl
            prjl
            (fun _ _ -> failwith "should not happen5")
            e
        in
        run one (fun q -> fresh (h) (inhabit_pair_lists (Std.nat 4) inhabit_int q))
          (fun r -> r#prjc prjp)
        |> OCanren.Stream.take ~n:(-1)
      in
      let demo_exprs =
        let rec hack_list = function
        | Std.List.Nil -> EConstr ("nil", Std.List.Nil)
        | Std.List.Cons (_,tl) ->
            EConstr ("cons", Std.List.of_list id [EConstr ("int", Std.List.Nil); hack_list tl])
        in
        ListLabels.map demo_exprs ~f:(fun (a,b) ->
          EConstr ("pair", Std.List.of_list id [ hack_list a; hack_list b])
        )
      in
(*      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;*)
(*      print_demos "demo_exprs" demo_exprs;*)
      let () =
        demo_exprs |> List.iter (fun e ->
(*          print_endline @@ Expr.show e;*)
          let open OCanren in
          run one (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
(*                  let (_:int)  = (OCanren.Stream.hd s) in*)
(*                  print_endline @@ IR.show_logic  ((OCanren.Stream.hd s)#reify IR.reify);*)
            )
          )
      in
      List.map Expr.inject demo_exprs
      (*let non_exh_pats = (Expr.econstr "DUMMY" []) :: non_exh_pats in
      (List.map Expr.inject demo_exprs, List.map Expr.inject non_exh_pats)*)
    in

    let count_constructors : IR.logic -> int = fun root ->
      let rec helper = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (_,scrul,then_,else_)) ->
          let scru_mb = Matchable.to_ground scrul in
          let () =
            match scru_mb with
            | Some scru_ground ->
              if (Matchable.height_ground scru_ground > 2) then raise FilteredOut
            | None -> ()
          in
          let a = helper then_ in
          let b = helper else_ in
          (1+a+b)
      in
      helper root
    in
    let height_hack ans =
      let max_ifs_count = 2 in (* TODO: populated for simple example *)
      let do_debug = false  in

      structural ans IR.reify (fun ir ->
        let debug fmt =
          Format.ksprintf (fun s -> if do_debug then Format.printf "%s" s else ())
            fmt
        in
        try
          debug "height_hack `%s` = %!" (IR.show_logic ir);
          let n = count_constructors ir in
          debug "%d%!" n;
          match n with
          | x when x>2 -> raise FilteredOut
          | _ ->
              debug "\n%!";
              true
        with FilteredOut ->
          debug " FILTERED OUT\n%!";
          false
      )
    in

(*
    let costf : IR.logic -> OCanren.cost = fun root ->
      let rec helper (low,var) = function
      | Var (_,_)     -> (low,true)
      | Value (Int _)
      | Value (Fail)  -> (0,false)
      | Value (IFTag (_,_,then_,else_)) ->
          let (lw,lf) = helper (0,false) then_ in
          let (rw,rf) = helper (0,false) else_ in
          (lw+rw+1, lf || rf)
      in
      let (n,has_var) = helper (0,false) root in
(*      Format.printf "costing `%s` = %d\n%!" (IR.show_logic root) n;*)
      let n = if n < 3 then 3 else n in
      if has_var
      then OCanren.CAtLeast n
      else OCanren.CFixed n
    in
*)

    let rec list_nth_nat idx xs ans =
      conde
        [ fresh (prev h tl)
            (Nat.one === idx)
            (xs === Std.(h % (ans % tl)))
        ; fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ]
    in

    let rec my_eval_m s h ans =
      conde
        [ (h === (scru ())) &&& (s === ans) &&& (fresh (a b) (Expr.constr !!"pair" Std.(a %< b) === ans))
        ; fresh (n m q23 cname es)
            (* field of scrutineee *)
            (scru () === m)
            (h === (field n m))
            (conde [  n === (Nat.s (z())); n === z () ])

(*            (conde
              [ cname === !!"nil"  &&&              (es === Std.nil())
              ; cname === !!"cons" &&& (fresh (a b) (es === Std.(a %< b)))
              ])*)

            (q23 === (eConstr cname es))
            (list_nth_nat n es ans)
            (my_eval_m s m q23)

        ; fresh (n m q23 q24 es)
            (h === (field n m))
            (m =/= scru())
            (conde [ n === z (); n === (Nat.s (z())) ])
            (q23 === (eConstr q24 es))
            (list_nth_nat n es ans)
            (my_eval_m s m q23)
        ]
    in

    let make_constraint var scru tag =
      (* we should not see the code which tests scru for this constructor *)
      structural var IR.reify (fun ir ->
        (*Format.printf "structural of '%s' with cname=%a and scru = %s\n"
          (IR.show_logic ir)
          (GT.fmt GT.string) tag
          (Matchable.show scru);*)

        let fail = false in
        let ok = true in
        let rec helper ir =
          match ir with
          | Var (_,_) -> ok
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru) && (_c = tag)
              then fail
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in
    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var IR.reify (fun ir ->
(*        Format.printf "structural2 of '%s' with scru = %s\n"
          (IR.show_logic ir)
          (Matchable.show scru);*)

        let rec helper ir =
          match ir with
          | Var (_,_) -> true
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru)
              then false
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

(*    let trace_tag tag =
      structural tag OCanren.reify (fun tag ->
        Format.printf "trace_var %s\n" (GT.show(OCanren.logic) (GT.show(GT.string)) tag);
        true
      )
    in*)

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s ir ans =
        let make_constraints_goal tag ~th ~el scru2 =
          let open Matchable in
          let wrap tag_str scur_g =
(*             (tag === !!tag_str) &&&*)
             (make_constraint th scur_g tag_str) &&&
             (make_constraint el scur_g tag_str)
          in
          conde
            [ (scru2 === scru   ()) &&& failure
            ; (scru2 === field0 ())

              (*&&& (wrap "nil"  (Field (Z,Scru)) )
              &&& (wrap "cons" (Field (Z,Scru)) )*)
              &&& (conde [ tag === !!"nil"; tag === !!"cons" ])
(*              &&& (make_constraint2 el (Field (Z,Scru)) )
              &&& (make_constraint2 th (Field (Z,Scru)) )*)


            ; (scru2 === field1 ())
              (*&&& (wrap "nil"  (Field (S Z,Scru)) )
              &&& (wrap "cons" (Field (S Z,Scru)) )*)
              &&& (conde [ tag === !!"nil"; tag === !!"cons" ])
(*              &&& (make_constraint2 el (Field (S Z,Scru)))
              &&& (make_constraint2 th (Field (S Z,Scru)))*)


            ; (scru2 === field00()) &&& failure
            ; (scru2 === field01()) &&& failure
            ; (scru2 === field10()) &&& failure
            ; (scru2 === field11()) &&& failure
            ]
        in
        conde
          [ (ir === (fail ())) &&& (ans === (none ()))
          ; fresh (n)
              (ir === (int n))
              (ans === (some n))

          ; fresh (tag scru2 th el q14 tag2 args q16 q6)
              (ir === (iFTag tag scru2 th el))
(*              (trace_tag tag)*)
              (q14 === (eConstr tag2 args))
              (conde [scru2 === scru   (); scru2 === Matchable.field0 ();  scru2 === Matchable.field1 () ])
              (my_eval_m s scru2 q14)

              (conde
                 [ (tag =/= tag2) &&&
(*                   (make_constraints_goal ~th ~el tag scru2) &&&*)
                   (self s el ans)
                 ; (tag === tag2) &&&
(*                   (make_constraints_goal ~th ~el tag scru2) &&&*)
                   (self s th ans)
                 ])
          ]
      in
      (fun a b c ->
        (height_hack ideal) &&&
        (*
        let rec y f x = f (fun z -> y f  z) x in
        y inner a b c
        *)
        (Tabling.(tabledrec three) inner a b c)
      )
    in

    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR 0 with hacks ", (fun ideal_IR ->
        let init = success in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (eval_pat             scru injected_pats res_pat)

            (conde
              [ fresh (n)
                 (res_pat === Std.Option.some (IR.int n))
                 (res_ir  === Std.Option.some n)
              ; (res_pat === Std.Option.none ()) &&& (res_ir === Std.Option.none())
              ])
            (my_eval_ir  ideal_IR scru ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));

    Format.printf "%!\n";
    ()


  (*
  For example all lists of <= two elements (height = 4) will be enough

    match xs,ys with
    | [],_ -> 10
    | _,[] -> 20
    | x::rx,y::ry -> 30
  *)

  let pattern_example1 =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 20
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 30
    ]

  let possible_answer =
    let run_ground clauses : IR.ground =
      let injected : Clauses.injected = Clauses.inject clauses in
      let first =
        OCanren.(run q (compile_naively injected)) (fun rr -> rr#prj)
        |> Stream.hd
      in
      (*print_endline "naive answer:";
      print_endline @@ IR.show first;*)
      let rec optimize (root: IR.ground)  =
        let rec helper = function
          | IFTag ("pair", Scru, then_, _) -> optimize then_
          | IFTag (c, scru, then_, else_) ->
              IFTag (c, scru, optimize then_, optimize else_)
          | x -> x
        in
        helper root
      in
      let second = optimize first in
      print_endline "\noptimized answer:";
      print_endline @@ IR.show @@ second;
      second
    in
    run_ground pattern_example1


  let _f  =
    run_hacky ~n:(10)
      pattern_example1

end
*)


module EvalMRez = struct
  type ground = (Expr.ground, GT.string Std.List.ground) Std.Pair.ground
(*      [@@deriving gt ~options: { show; fmt }]*)
  type logic = (Expr.logic, GT.string OCanren.logic Std.List.logic) Std.Pair.logic
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


open Main_inputs



(*

module N0 = Impl1.Make(struct
  include ArgMake(ArgSimpleList)
end)

let () = N0.test ()
*)

module N1 = Impl1.Make(struct
  include ArgMake(ArgTwoNilShort)
end)

(*let () = N1.test ()*)

module N2 = Impl1.Make(struct
  include ArgMake(ArgTwoNilLonger)
end)

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

(*
module TwoNilList3 = struct

  let inhabit_pair_lists = TwoNilList.inhabit_pair_lists
  let inhabit_int = Helper.inhabit_int

  let possible_answer = TwoNilList.possible_answer

  module L = TwoNilList.L

  let synth_twonillist3 ?(n=10) clauses typs =
    let max_height =
      let n = List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
      Format.printf "patterns max height = %d\n%!" n;
      Nat.inject @@ Nat.of_int n
    in

    let check_scrutinee root =
      let rec helper len = function
      | Value Scru -> len+1
      | Value (Field (_, next)) -> helper (len+1) next
      | Var (_,_) -> len
      in
      let ans = helper 0 root in
  (*      Format.printf "check_scrutinee: length `%s` = %d\n%!" (Matchable.show_logic root) ans;*)
      ans
    in
    let count_constructors : IR.logic -> int = fun root ->
      let rec helper seen = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (tag_log,scru,then_,else_)) ->
          let () =
            if check_scrutinee scru > 2 then raise FilteredOut
          in
          let seen_new =
            match (tag_log,Matchable.to_ground scru) with
            | (Value s, Some mat_ground) ->
                if Matchable.height_ground mat_ground > 2 then raise FilteredOut;
                let candidate = (s,mat_ground) in
                if List.mem candidate seen
                then raise FilteredOut
                else
  (*                  let () = printf "Adding candidate (%s,%s)\n%!" s (Matchable.show mat_ground) in*)
                  candidate::seen
            | _ -> seen
          in
          let a = helper seen_new then_ in
          let b = helper seen_new else_ in
          (1+a+b)
      in
      helper [] root
    in

  let height_hack ans =
    let max_ifs_count = 6 in (* TODO: populated for simple example *)
    let do_debug = false in

    let prev = ref (Obj.magic false) in
    structural ans IR.reify (fun ir ->
      let verbose = not (!prev = ir) in
      prev := ir;
      let debug fmt =
        Format.ksprintf (fun s -> if do_debug&&verbose then Format.printf "%s" s else ())
          fmt
      in
      try
        debug "height_hack `%s` = %!" (IR.show_logic ir);
        let n = count_constructors ir in
        debug "%d%!" n;
        match n with
        | x when x > max_ifs_count -> raise FilteredOut
        | _ ->
            debug "\n%!";
            true
      with FilteredOut ->
        debug " FILTERED OUT\n%!";
        false
    )
  in

    let hack ideal goal =
      (height_hack ideal) &&&
      goal
    in

    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->
        let rec helper ir =
          match ir with
          | Var (_,_) -> true
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              let matchable_ground = Matchable.to_ground m in
              if (matchable_ground = Some scru)
              then false
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

    let make_constraint var scru tag =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->

        let fail = false in
        let ok = true in
        let rec helper ir =
          match ir with
          | Var (_,_) -> ok
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru) && (_c = tag)
              then fail
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in
(*
    let my_membero xs x =
      fresh (foo)
(*        (debug_var xs (fun x env -> Std.List.reify OCanren.reify env x )
          (fun xs -> Format.printf "mymembero %s\n%!"
            (GT.show GT.list (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)) xs)))
        (debug_var x  (fun x env -> OCanren.reify env x)
          (fun xs -> Format.printf "          %s\n%!"
            (GT.show GT.list (GT.show OCanren.logic @@ GT.show GT.string) xs)))*)
        (Std.List.membero xs x)
    in
*)

    let rec list_nth_nat idx xs q114 =
      let open Std in
      fresh (q115)
        (q115 === (pair idx xs))
        ((fresh (x q116)
            (q115 === (pair (z ()) (x % q116)))
              (x === q114))
              |||
              (fresh (n q118 xs)
                (q115 === (pair (s n) (q118 % xs)))
                (list_nth_nat n xs q114)))
    in

    let (_: Typs.injected ->
            (string, string OCanren.logic) injected ->
            (Typs.ground, Typs.logic) Std.List.groundi ->
            goal) = info_assoc
    in

    (* HACKED TERRIBLY *)
    let rec list_nth_nat idx xs ans =
      (*let open Std in *)
      conde
        [ fresh (prev h tl)
            (Nat.one === idx)
            (xs === Std.(h % (ans % tl)))
        ; fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ]
    in
    (*
    let rec list_nth_nat idx xs q114 =
      let (%) = Std.(%) in
      let pair = Std.Pair.pair in
      fresh (q115)
        (q115 === (Std.Pair.pair idx xs))
        (conde
          [ (fresh (x q116)
            (q115 === (Std.Pair.pair (z ()) (x % q116)))
              (x === q114))
          ; (fresh (n q118 xs)
                (q115 === (pair (s n) (q118 % xs)))
                (list_nth_nat n xs q114))
          ])
    in
    *)
    let rec eval_m s typinfo0 path0 q52 =
      let pair = Std.Pair.pair in
      let rec helper path q40 =
        ((path === (scru ())) &&& (q40 === (pair s typinfo0))) |||
          (fresh (nth scru q43 cname es next_tinfos arg_info q45 q46)
            (path === (field nth scru))
            (q43 === (pair (eConstr cname es) next_tinfos))
            (q40 === (pair q45 q46))
            (helper scru q43)
            (info_assoc next_tinfos cname arg_info)
            (list_nth_nat nth es q45)
            (list_nth_nat nth arg_info q46))
      in
      fresh (q49 ans info q50)
        (q49 === (pair ans info))
        (q52 === (pair ans q50))
        (helper path0 q49)
        (tinfo_names info q50)
    in

    let my_eval_ir ideal s max_height tinfo ir (rez as q39) =
      let open Std in
      let inner =
        Tabling.tabledrec Tabling.two
          (fun inner irrr q23 ->
             conde
               [ (irrr === (fail ())) &&& (q23 === (none ()))
               ; fresh (n) (irrr === (int n)) (q23 === (some n))
               ; fresh (tag scru th el q27 q37 q29 tag2 args cnames q31 q33)
                   (irrr === (iFTag tag scru th el))
                   (q27 === (!! true))
                   (q29 === (pair (eConstr tag2 args) cnames))
                   (q31 === (!! true))
                   (height_of_matchable scru q37)
                   (nat_leq q37 max_height q27)
                   (eval_m s tinfo scru q29)
                   (list_mem tag cnames q31)
                   (conde
                     [ (tag2 === tag) &&& (q33 === (!! true))
                     ; (q33 === (!! false)) &&& (tag2 =/= tag)
                     ])
                   (conde
                     [ (q33 === (!! true)) &&& (inner th q23)
                     ; (q33 === (!! false)) &&& (inner el q23)
                     ])
               ])
      in
      (height_hack ideal) &&&
      (inner ir q39)

       (*
        (Work.eval_ir s max_height tinfo ir rez)
        *)
    in



    let injected_pats = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
        let prjl e =
          L.prjc
            prj1
            (fun _ _ -> failwith "should not happen2")
            e
          in
        let prjp e =
          Std.Pair.prjc
            prjl
            prjl
            (fun _ _ -> failwith "should not happen5")
            e
        in
        run one (fun q -> fresh (h) (inhabit_pair_lists (Std.nat 4) inhabit_int q))
          (fun r -> r#prjc prjp)
        |> OCanren.Stream.take ~n:(-1)
      in
      let demo_exprs =
        let rec hack_list = function
        | L.Nil -> EConstr ("nil", Std.List.Nil)
        | L.Nil2 -> EConstr ("nil2", Std.List.Nil)
        | L.Cons (_,tl) ->
            EConstr ("cons", Std.List.of_list id [EConstr ("int", Std.List.Nil); hack_list tl])
        in
        ListLabels.map demo_exprs ~f:(fun (a,b) ->
          EConstr ("pair", Std.List.of_list id [ hack_list a; hack_list b])
        )
      in
  (*      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;*)
  (*      print_demos "demo_exprs" demo_exprs;*)
      let () =
        demo_exprs |> List.iter (fun e ->
(*          Format.printf "%s --> %!" (Expr.show e);*)
          let open OCanren in
          run one (fun ir ->
              let answer_demo = IR.inject possible_answer in
              let scru_demo = Expr.inject e in
              fresh (n rez)
                (eval_pat scru_demo injected_pats rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (my_eval_ir answer_demo scru_demo max_height typs answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  (*Format.printf "%s\n%!"
                    (IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify));*)
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR 1 no hacks at all (not)", (fun ideal_IR ->
        let init = success in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (eval_pat             scru injected_pats res_pat)

            (conde
              [ fresh (n)
                 (res_pat === Std.Option.some (IR.int n))
                 (res_ir  === Std.Option.some n)
              ; (res_pat === Std.Option.none ()) &&& (res_ir === Std.Option.none())
              ])
            (my_eval_ir  ideal_IR scru max_height typs ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));
    Format.printf "%!\n";
    ()

  let _f () =
    synth_twonillist3 ~n:(2)
      TwoNilList.two_nil_demo_clauses1 TwoNilList.typs1


end
*)


module FTrueFalse = Algo_fair.Make(struct
  include ArgMake(ArgTrueFalse)
end)
(*let () = FTrueFalse.test ~n:10*)

module FPairTrueFalse = Algo_fair.Make(struct
  include ArgMake(ArgPairTrueFalse)
  let max_ifs_count = 2
(*
  let inhabit (_:int) (rez : qtyp_injected) =
    let pair a b = Std.Pair.pair a b in
    let zero = Nat.z in
    let su x = Nat.s x in
    conde
      [ rez === pair zero zero
      ; rez === pair (su zero) (zero)
      ; rez === pair zero (su zero)
      ; rez === pair (su zero) (su zero)
      ]
      *)
end)
(*let () = FPairTrueFalse.test ~n:(-1) ~with_hack:true*)

module FABC = Algo_fair.Make(struct
  include ArgMake(ArgABC)
  let max_ifs_count = 1
end)
(*let () = FABC.test ~n:10*)



module F1 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
  let max_ifs_count = 2
end)
module F2 = Algo_fair.Make(ArgMake(ArgTwoNilShort))

(*let () = F1.test ~n:10*)

(*let () = F2.test ~n:2*)

module F3 = Algo_fair.Make(struct
  include ArgMake(ArgPeanoSimple)
  let max_ifs_count = 2
(*  let max_height = 2*)
(*
  let inhabit (_:int) (rez : qtyp_injected) =
    let pair a b = Std.Pair.pair a b in
    let zero = Nat.z in
    let su x = Nat.s x in
    conde
      [ rez === pair zero zero
      ; rez === pair (su zero) (zero)
      ; rez === pair zero (su zero)
      ; rez === pair (su zero) (su zero)
      ]*)

  let ir_hint ir =
    fresh (a b c d t1 t2 )
      success

  (*    (ir === iFTag t1 (Matchable.field0())
          a
          b)*)


(*      (t1 === !!"succ")*)
(*      (a === (iFTag !!"succ" (Matchable.field1()) c d ))*)

end)

(*let () = F3.test 40*)

module Fair2_1 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
end)

(*
module Fair2_2 = Algo_fair2.Make(struct
  include ArgMake(ArgTwoNilShort)
end)
*)

let () = Fair2_1.test 10
(*let () = Fair2_2.test ~n:2*)

(* *************************************************************************** *)
module Fair3_1 = Algo_fair.Make(struct
  include ArgMake(ArgSimpleList)
end)

let () = Fair3_1.test 10



module Fair4_1 = Algo_fair.Make(struct
  include ArgMake(ArgTwoNilSimpl)
(*  let max_ifs_count = 3*)
end)

let () = Fair4_1.test 20










