(* Executes exactly what is written in lozovML
 *
 * Downside: doesn't know that match in Pair is not okay
 *)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR

module Make(Arg: ARG_FINAL) = struct

  let work ?(n=10) ~with_hack ~print_examples clauses typs =
    let possible_answer = Arg.possible_answer in
    assert (Arg.max_ifs_count <= (IR.count_ifs_ground possible_answer));
    let max_ifs_count = ref Arg.max_ifs_count in
    Format.printf "preliminary answer:\n%s\n%!" (IR.show possible_answer);
    Format.printf "max IFs count = %d,\tArg.max_height = %d\n%!" !max_ifs_count Arg.max_height;

    let upgrade_bound x =
      if !max_ifs_count > x
      then
        let () = Format.printf "minimal bound is set to %d\n%!" x in
        max_ifs_count := x
    in


    let max_height = Nat.inject @@ Nat.of_int Arg.max_height in

    (** Raises [FilteredOut] when answer is not worth it *)
    let count_if_constructors : IR.logic -> int = fun root ->
      let rec helper seen = function
      | Var (_,_)
      | Value (Int _)
      | Value Fail -> 0
      | Value (IFTag (tag_log,scru,then_,else_)) ->

          (*let () =
            if Matchable.low_height_of_logic scru > Arg.max_height
            then raise FilteredOut
          in
          *)
(*
          let seen_new =
            match (tag_log, Matchable.to_ground scru) with
            | (Value s, Some mat_ground) ->
                let candidate = (s,mat_ground) in
                if List.mem candidate seen
                then
                  raise FilteredOut
                else
  (*                  let () = printf "Adding candidate (%s,%s)\n%!" s (Matchable.show mat_ground) in*)
                  candidate::seen
            | _ -> seen
          in
*)
          let seen_new = seen in
          let a = helper seen_new then_ in
          let b = helper seen_new else_ in
          (1+a+b)
      in
      helper [] root
    in

  let _ifs_size_hack (ans: IR.injected) =
    let _do_debug = true in
    let _do_debug = false in

(*    let prev = ref (Obj.magic false) in*)
    structural ans IR.reify (fun ir ->
(*      let verbose = not (!prev = ir) in*)
      let verbose = true in
(*      prev := ir;*)
      let debug fmt =
        Format.ksprintf (fun s -> if _do_debug&&verbose then Format.printf "%s" s else ())
          fmt
      in
      try
        debug "height_hack `%s` = %!" (IR.show_logic ir);
        let n = count_if_constructors ir in
        assert (n >= 0);
        debug "%d%!" n;
        match n with
        | x when x > !max_ifs_count ->
(*          let () = Format.printf "  %s (size = %d) FILTERED OUT because of Ifs count \n%!" (IR.show_logic ir) x in*)
          raise FilteredOut
        | _ ->
            debug "\n%!";
            true
      with FilteredOut ->
        debug " FILTERED OUT\n%!";
        false
    )
  in

    let my_eval_ir ideal s tinfo ir rez =
      (if with_hack then _ifs_size_hack ideal else success) &&&
      (Work.eval_ir s max_height tinfo Arg.shortcut ir rez)
    in

    let injected_clauses = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        run one (fun q -> Arg.inhabit Arg.max_height q) (fun r -> r#prjc Arg.prjp)
        |> OCanren.Stream.take ~n:(-1)
        |> Arg.wrap_demo
      in


      let () =
        if print_examples
        then Format.printf "Testing %d examples:\n%!" (List.length demo_exprs);

        demo_exprs |> List.iter (fun e ->
          if print_examples then Format.printf "  %s ~~> %!" (Expr.show e);
          let open OCanren in
          run one (fun ir ->
              let answer_demo = IR.inject possible_answer in
              let scru_demo = Expr.inject e in
              fresh (n rez)
                (Work.eval_pat scru_demo injected_clauses rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (Work.eval_ir  scru_demo max_height typs simple_shortcut answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  if print_examples
                  then Format.printf "%s\n%!" @@
                        IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify);
            )
          )
      in
      List.map Expr.inject demo_exprs
    in


    Helper.show_local_time ();
    let info = Format.sprintf "fair lozovML (%s)" Arg.info in
    let on_ground ir =
      let nextn = IR.count_ifs_ground ir in
      upgrade_bound nextn;
      IR.show ir
    in
    let on_logic ir =
      let nextn = IR.count_ifs_low ir in
      upgrade_bound nextn;
      IR.show_logic ir
    in
    let open Mytester in
    runR IR.reify on_ground on_logic n q qh (info, (fun ideal_IR ->
        let init = Arg.ir_hint ideal_IR in

        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (Work.eval_pat             scru injected_clauses res_pat)
            (conde
              [ fresh (n)
                  (res_pat === Std.Option.some (IR.int n))
                  (res_ir  === Std.Option.some n)
              ; fresh ()
                  (res_pat === Std.Option.none ())
                  (res_ir === Std.Option.none())
              ])
              (my_eval_ir  ideal_IR scru typs ideal_IR res_ir)
          )
          init
          injected_exprs
      ));
    Format.printf "%!\n"



  let test ?(with_hack=true) ?(print_examples=true) n =
    work ~n ~with_hack ~print_examples Arg.clauses Arg.typs

end

