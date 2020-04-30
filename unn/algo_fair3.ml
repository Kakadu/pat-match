(*
  Trying to fix algo_fair2 by adding structural constraints
  *)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR

let simple_shortcut _ _ _ ans = (ans === !!true)

module Make(Arg: ARG_FINAL) = struct

  let work ?(n=10) clauses typs =
    let possible_answer = Arg.possible_answer in
    let max_ifs_count = ref Arg.max_ifs_count in
      (* IR.count_ifs_ground possible_answer  *)
    Format.printf "max IFs count = %d\n%!" !max_ifs_count;

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
        | x when x > !max_ifs_count ->
(*            Format.printf "  %s (size = %d) FILTERED OUT\n%!" (IR.show_logic ir) x;*)
            raise FilteredOut
        | _ ->
            debug "\n%!";
            true
      with FilteredOut ->
        debug " FILTERED OUT\n%!";
        false
    )
  in

(*

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



    let structural_hack3 tag scru th =
      let reifier env x = Std.Pair.reify OCanren.reify (Std.Pair.reify Matchable.reify IR.reify) env x in

      structural (Std.Pair.pair tag (Std.Pair.pair scru th)) reifier
        (fun (triple: (string OCanren.logic * (Matchable.logic * IR.logic) OCanren.logic) OCanren.logic ) ->
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
*)


    let my_eval_ir ideal s tinfo ir rez =
      let make_constraint var scru tag =
        (* we should not see the code which tests scru for this constructor *)
        structural var IR.reify (fun ir ->
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
      let shortcut tag scru_ th rez =
        let open Matchable in
        (rez === !!true) &&&
        conde
          [ (tag === !!"pair") &&& failure
          ; (Matchable.scru () === scru_) &&& failure
          ; (tag =/= !!"pair") &&&
            (conde
              [ (tag === !!"cons") &&& (scru_ === field0()) &&& (make_constraint th (Field(Z,Scru)) "cons")
              ; (tag === !!"nil")  &&& (scru_ === field0()) &&& (make_constraint th (Field(Z,Scru)) "nil")
              ; (tag === !!"nil2") &&& (scru_ === field0()) &&& (make_constraint th (Field(Z,Scru)) "nil2")
              ; (tag === !!"cons") &&& (scru_ === field1()) &&& (make_constraint th (Field(S Z,Scru)) "cons")
              ; (tag === !!"nil")  &&& (scru_ === field1()) &&& (make_constraint th (Field(S Z,Scru)) "nil")
              ; (tag === !!"nil2") &&& (scru_ === field1()) &&& (make_constraint th (Field(S Z,Scru)) "nil2")
              ])
          ]

      in

      (height_hack ideal) &&&
      (* (inner ir rez) *)
      (Work.eval_ir s max_height tinfo shortcut ideal rez)
    in

    let injected_pats = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        run one (fun q -> Arg.inhabit Arg.max_height q) (fun r -> r#prjc Arg.prjp)
        |> OCanren.Stream.take ~n:(-1)
        |> Arg.wrap_demo
      in

      let () =
        demo_exprs |> List.iter (fun e ->
          Format.printf "%s --> %!" (Expr.show e);
          let open OCanren in
          run one (fun ir ->
              let answer_demo = IR.inject possible_answer in
              let scru_demo = Expr.inject e in
              fresh (n rez)
                (Work.eval_pat scru_demo injected_pats rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (Work.eval_ir scru_demo max_height typs simple_shortcut answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  Format.printf "%s\n%!"
                    (IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify));
            )
          )
      in
      List.map Expr.inject demo_exprs
    in


    Helper.show_local_time ();
    let info = Format.sprintf "algo fair 3 -- adding structural (%s)" Arg.info in
    let open Mytester in
    runR IR.reify IR.show IR.show_logic n
      q qh (info, (fun ideal_IR ->
        let init = success in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (Work.eval_pat             scru injected_pats res_pat)
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


  let test ~n =
    work ~n Arg.clauses Arg.typs

end

