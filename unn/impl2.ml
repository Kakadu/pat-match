(* ???
 *
 **)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR

module Make(Arg: ARG_FINAL) = struct
  let synth_twonillist2 ?(n=10) clauses typs =
    let possible_answer = Arg.possible_answer in
    let max_ifs_count = IR.count_ifs_ground possible_answer in
    Format.printf "max IFs count = %d\n%!" max_ifs_count;

    let max_height = Nat.inject @@ Nat.of_int Arg.max_height in

    let count_if_constructors : IR.logic -> int = fun root ->
      let rec helper seen = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (tag_log,scru,then_,else_)) ->
          let () =
            if Matchable.low_height_of_logic scru > Arg.max_height
            then raise FilteredOut
          in
          let seen_new =
            match (tag_log,Matchable.to_ground scru) with
            | (Value s, Some mat_ground) ->
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
    let do_debug = true in
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
        let n = count_if_constructors ir in
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


(*
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
*)
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

(*
  let rec list_mem x xs q178 =
    let open Std in
    conde
      [ ((xs === (nil ())) &&& (q178 === (!! false)))
      ; fresh (h tl q181)
         (xs === (h % tl))
         (conde
           [ (x === h) &&& (q181 === (!! true))
           ; (q181 === (!! false)) &&& (x =/= h)
           ])
         (conde
           [ (q181 === (!! true)) &&& (q178 === (!! true))
           ; (q181 === (!! false)) &&& (list_mem x tl q178)
           ])
      ]
    in
    *)

    let rec list_mem x xs (q178 as ans) =
      let open Std in
      conde
        [ ((xs === (nil ())) &&& (q178 === (!! false)))
        ; fresh (h tl q181)
           (xs === (h % tl))
           (conde
             [ (x === h) &&& (q178 === (!! true))
             ; (x =/= h) &&& (list_mem x tl q178)
             ])
        ]
    in

    let structural_hack3 tag scru th =
      let reifier env x = Std.Pair.reify OCanren.reify (Std.Pair.reify Matchable.reify IR.reify) env x in

      structural (Std.Pair.pair tag (Std.Pair.pair scru th)) reifier
        (fun (triple: (string logic * (Matchable.logic * IR.logic) logic) OCanren.logic ) ->
          let fail = false in
          let ok = true in
(*          print_endline "something was reified";*)
          match triple with
          | Value (Value tag, Value ((Value _) as m, ((Value _) as ir))) ->
            begin
            try
              let rec helper (ir: IR.logic) =
                match ir with
                | Var (_,_) -> ok
                | Value (IFTag (Value _c, m1, th_, el_)) -> begin
                    if (m1 = m) && (_c = tag)
                    then raise FilteredOut
                    else (helper th_) && (helper el_)
                end
                | _ -> ok
              in
              helper ir
            with FilteredOut -> fail
            end
         | _ -> ok
        )
    in

    let my_membero xs x =
(*      fresh (foo)*)
        (*
        (debug_var xs (fun x env -> Std.List.reify OCanren.reify env x )
          (fun xs -> Format.printf "mymembero %s\n%!"
            (GT.show GT.list (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)) xs)))
        (debug_var x  (fun x env -> OCanren.reify env x)
          (fun xs -> Format.printf "          %s\n%!"
            (GT.show GT.list (GT.show OCanren.logic @@ GT.show GT.string) xs)))
            *)
        (Std.List.membero xs x)
(*        (list_mem x xs !!true)*)
    in
(*
    let rec eval_m s typinfo0 path0 q52 =
      let open Std in
      let rec helper path q40 =
        conde
         [ ((path === (scru ())) &&& (q40 === (pair s typinfo0)))
         ; fresh (nth scru q43 cname es next_tinfos arg_info q45 q46)
             (path === (field nth scru))
             (q43 === (pair (eConstr cname es) next_tinfos))
             (q40 === (pair q45 q46))
             (helper scru q43)
             (info_assoc next_tinfos cname arg_info)
             (list_nth_nat nth es q45)
             (list_nth_nat nth arg_info q46)
         ]
      in
      fresh (q49 ans info q50)
        (q49 === (pair ans info))
        (q52 === (pair ans q50))
        (helper path0 q49)
        (tinfo_names info q50)
    in
    *)



    let my_eval_ir ideal s tinfo ir rez =
      let open Std in
      let rec inner =
        Tabling.(tabledrec two)
        (fun inner irrr ans ->
          conde
            [ (irrr === (fail ())) &&& (ans === (none ()))
            ; fresh (n) (irrr === (int n)) (ans === (some n))
            ; fresh (tag scru th el q35 q29 tag2 args cnames q31 nnn)
                (irrr === (iFTag tag scru th el))
                (q29 === (pair (eConstr tag2 args) cnames))
                (matchable_leq_nat scru max_height !!true)
                (eval_m s tinfo scru q29)
                (Std.List.membero cnames tag)             (* with this stuff only it works 200-226 secs *)
                (conde [ (tag === !!"pair") &&& failure ; (tag =/= !!"pair") ] )  (* reduces to 163 seconds *)
(*
                (conde
                  [ (tag2 === tag) &&& (q31 === (!! true))
                  ; (q31 === (!! false)) &&& (tag2 =/= tag)])
                (conde
                  [ (q31 === (!! true)) &&& (inner th ans)
                  ; (q31 === (!! false)) &&& (inner el ans)
                  ])
*)
                (conde
                  [ (tag2 === tag) &&& (inner th ans)
                  ; (tag2 =/= tag) &&& (inner el ans) ])
            ]
        )
      in
      (height_hack ideal) &&& (inner ir rez)
    in

    let injected_pats = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
(*        *)
        run one (fun q -> Arg.inhabit Arg.max_height q) (fun r -> r#prjc Arg.prjp)
        |> OCanren.Stream.take ~n:(-1)
      in
      let demo_exprs : Expr.ground list = Arg.wrap_demo demo_exprs in

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
                (my_eval_ir answer_demo scru_demo typs answer_demo (Std.Option.some n))
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

(*    let injected_exprs = List.rev injected_exprs in*)

    Helper.show_local_time ();
    let info = Format.sprintf "idealIR minimal hacks (%s)" Arg.info in
    runR IR.reify IR.show IR.show_logic n
      q qh (info, (fun ideal_IR ->
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
            (my_eval_ir  ideal_IR scru typs ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));
    Format.printf "%!\n"


  let test () =
    synth_twonillist2 ~n:2
      Arg.clauses
      Arg.typs


end
