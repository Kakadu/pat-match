(* Executes exactly what is writtenin lozovML
 *
 * Downside: doesn't know that match in Pair is not okay
 *)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR

module Make(Arg: ARG_FINAL) = struct

  let work ?(n=10) clauses typs =
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


    let shortcut _tag _Scru _th rez = (rez === !!true) in

    let my_eval_ir ideal s tinfo ir rez =
      (height_hack ideal) &&&
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
                (my_eval_ir answer_demo scru_demo typs answer_demo (Std.Option.some n))
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
    let info = Format.sprintf "fair lozovML (%s)" Arg.info in
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

