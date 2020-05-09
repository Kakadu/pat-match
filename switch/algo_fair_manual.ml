(* Executes exactly what is written in lozovML
 *
 * Downside: doesn't know that match in Pair is not okay
 *)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR


module Work = struct
  include Work

let rec not_in_history x xs =
  let open Std in
  conde
    [ (xs === Std.nil ())
    ; fresh (h tl)
        (xs === Std.(h%tl))
        (x =/= h)
        (not_in_history x tl)
    ]

let rec eval_ir s max_height tinfo shortcut1 shortcut_tag ir q32 =
  let open OCanren.Std in
  let rec inner history test_list  irrr q11 =
    conde
      [ (irrr === (fail ())) &&& (q11 === (none ()))
      ; fresh (n)
          (irrr === (lit n))
          (q11 === (some n))
      ; fresh (m xs on_default q15 q17 etag args cnames q19)
          (irrr === (switch m xs on_default))
          (q17 === (pair (eConstr etag args) cnames))
          (matchable_leq_nat m max_height !!true)                  (* commenting this line is not recommended *)
          (eval_m s tinfo m q17)
          (shortcut1 etag m xs !!true)
(*          (not_in_history q17 history)*)
          (test_list (m%history) etag  cnames on_default xs q11)
      ]
  in
  let rec test_list next_histo etag cnames on_default cases q30 =
    let rec helper prev xs q20 =
      conde
        [ ((xs === (nil ())) &&& (inner next_histo test_list on_default q20))
        ; fresh (qtag ontag tl)
            (xs === ((pair qtag ontag) % tl))
            (list_mem qtag cnames !!true)
            (shortcut_tag prev qtag !!true)
            (conde
              [ (qtag === etag) &&& (inner next_histo test_list ontag q20)
              ; (qtag =/= etag)  &&& (helper (some qtag) tl q20)
              ])
        ]
    in
    helper (none ()) cases q30
  in
  inner (nil()) test_list ir q32
end

let (_: Expr.injected -> Nat.injected -> Typs.injected -> _ -> _ -> IR.injected -> _ -> goal) = Work.eval_ir

let disable_periodic_prunes () =
  let open OCanren.PrunesControl in
  enable_skips ~on:false

exception FilteredOutBySize of int
exception FilteredOutByForm


module Make(Arg: ARG_FINAL) = struct

  let work ?(n=10) ~with_hack ~print_examples ~check_repeated_ifs ~debug_filtered_by_size ~prunes_period clauses typs =
    print_endline "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    Clauses.pretty_print Format.std_formatter clauses;
    let possible_answer = Arg.possible_answer in
    assert (Arg.max_ifs_count <= (IR.count_ifs_ground possible_answer));
    let max_ifs_count = ref Arg.max_ifs_count in
    Format.printf "A priori answer:\n%a\n%!" (GT.fmt IR.ground) possible_answer;
    Format.printf "Initial upper bound of IF-ish constructions = %d,\tmax_matchable_height = %d\n%!" !max_ifs_count Arg.max_height;

    let upgrade_bound x =
      if !max_ifs_count > x
      then
        let () = Format.printf "Set upper bound of IF-ish constructions to %d\n%!" x in
        max_ifs_count := x
    in


    let max_height = Nat.inject @@ Nat.of_int Arg.max_height in

    (** Raises [FilteredOut] when answer is not worth it *)
    let count_if_constructors : IR.logic -> int = fun root ->
      let next_seen seen scru tag =
        if not check_repeated_ifs
        then seen
        else
            match (Matchable.to_ground scru) with
            | Some mground ->
                if List.mem mground seen
                then raise FilteredOutByForm
                else mground :: seen
            | _ -> seen
      in
      let rec helper acc seen = function
      | Var (_,_)
      | Value (Lit _)
      | Value Fail -> acc
      | Value (Switch (_, Value Std.List.Nil, _)) -> raise FilteredOutByForm
      | Value (Switch (scru, xs, on_default)) ->
          GT.foldl Std.List.logic (fun acc -> function
            | Value (Var _, code) -> helper acc seen code
            | Value (tagl, code) ->
                let seen = next_seen seen scru tagl in
                helper acc seen code
            | Var _ -> acc)
            0
            xs
          +
          (helper (acc + (logic_list_len_lo xs)) seen on_default)
      in
      helper 0 [] root
    in

    let _ifs_size_hack (ans: IR.injected) =
      let _do_debug = true in
      let _do_debug = false in

      structural ans IR.reify (fun (ir: IR.logic) ->
        let verbose = true in
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
            raise (FilteredOutBySize x)
          | _ ->
              debug "\n%!";
              true
        with
          | FilteredOutBySize n ->
            if debug_filtered_by_size
            then Format.printf "  %s (size = %d) FILTERED OUT because of Ifs count \n%!"
              (IR.show_logic ir) n ;
            false
          | FilteredOutByForm ->
            if debug_filtered_by_size
            then Format.printf "  %s FILTERED OUT because of form \n%!"
                (IR.show_logic ir) ;
            false
      )
    in

(*    let (_: Expr.injected -> Nat.injected -> Typs.injected -> _ -> IR.injected -> _ -> goal) = Work.eval_ir in*)
(*    let (_: IR.injected -> Expr.injected -> Typs.injected -> IR.injected -> _ -> goal) = my_eval_ir in*)

    let injected_clauses = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        run one (fun q -> Arg.inhabit Arg.max_height q) (fun r -> r#prjc Arg.prjp)
        |> OCanren.Stream.take ~n:(-1)
        |> Arg.to_expr
      in

      let () =
        if print_examples
        then Format.printf "Testing %d examples:\n%!" (List.length demo_exprs);

        demo_exprs |> List.iter (fun e ->
          if print_examples then Format.printf "  %s ~~> %!" (Expr.show e);
          let answer_demo = IR.inject possible_answer in
          let scru_demo = Expr.inject e in
          let open OCanren in
          run one (fun ir ->
              fresh (n rez)
                (Work.eval_pat scru_demo injected_clauses rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (Work.eval_ir scru_demo max_height typs simple_shortcut simple_shortcut_tag answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  let () =
                    if OCanren.Stream.is_empty s
                    then
                      let () =
                        let open Mytester in
                        runR (Std.Option.reify OCanren.reify) (GT.show Std.Option.ground @@ GT.show GT.int)
                            (GT.show Std.Option.logic (GT.show logic @@ GT.show GT.int)) 1 q qh
                          ("eval_ir", (Work.eval_ir scru_demo max_height typs simple_shortcut simple_shortcut_tag answer_demo))
                      in
                      failwith "Bad (?) example"
                  in
                  if print_examples
                  then Format.printf "%s\n%!" @@
                        IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify);
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

    let () =
      match prunes_period with
      | Some n when n <= 0 -> failwith "bad prunes period"
      | Some n ->
          let open OCanren.PrunesControl in
          set_max_skips n;
          enable_skips ~on:true;
          reset ()
      | None -> disable_periodic_prunes ()
    in
    let info = Format.sprintf "MANUAL lozovML (%s)" Arg.info in
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

    let my_eval_ir ideal (s: Expr.injected) tinfo ir rez =
      (if with_hack then _ifs_size_hack ideal else success) &&&
      (Work.eval_ir s max_height tinfo Arg.shortcut Arg.shortcut_tag ir rez)
    in

    let start = Mtime_clock.counter () in

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
    let span = Mtime_clock.count start in
    let () = disable_periodic_prunes () in

    Format.printf "\n";
    Format.printf "Total synthesis time: %s\n%!"
      ( let ms = Mtime.Span.to_ms span in
        if ms > 10000.0
        then Format.sprintf "%10.0fs \n%!" (Mtime.Span.to_s span)
        else Format.sprintf "%10.0fms\n%!" ms)



  let test ?(print_examples=true) ?(debug_filtered_by_size=false)
      ?(with_hack=true) ?(check_repeated_ifs=false)
      ?(prunes_period=(Some 100))
      n =
    work ~n ~with_hack ~print_examples ~check_repeated_ifs ~debug_filtered_by_size
      ~prunes_period
      Arg.clauses Arg.typs

end

