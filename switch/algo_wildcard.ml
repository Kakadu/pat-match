(* Executes exactly what is written in lozovML
 *
 *)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR

let eval_examples (module W : WORK) (module Arg : ARG_FINAL) =
  let injected_clauses = Clauses.inject Arg.clauses in
  let demo_exprs =
    run one Arg.inhabit (fun r -> r#prjc Expr.prjc) |> OCanren.Stream.take ~n:(-1)
  in
  let demo_exprs =
    demo_exprs
    |> List.map (fun e ->
           let scru_demo = Expr.inject e in
           let stream =
             OCanren.(run one)
               (fun rez -> W.eval_pat scru_demo injected_clauses rez)
               (fun r -> r)
           in
           let () = if OCanren.Stream.is_empty stream then failwith "Bad (?) example" in
           let rez = (OCanren.Stream.hd stream)#reify (Std.Option.reify IR.reify) in
           e, rez)
  in
  demo_exprs
;;

let disable_periodic_prunes () =
  let open OCanren.PrunesControl in
  enable_skips ~on:false
;;

exception FilteredOutBySize of int
exception FilteredOutByForm
exception FilteredOutByNestedness
exception FilteredOutByTooManyCases
exception FilteredOutByTagsOrder

let is_enabled = ref true

module Make (W : WORK) (Arg : ARG_FINAL) = struct
  module MatchableMap = Map.Make (struct
    type t = Matchable.ground

    let compare x y =
      let ans = Matchable.ground.plugins#compare x y in
      GT.cmp_to_int ans
    ;;
  end)

  let matchables_counts : int MatchableMap.t ref = ref MatchableMap.empty

  let incr_mc k =
    try
      let n = MatchableMap.find k !matchables_counts in
      matchables_counts := MatchableMap.add k (n + 1) !matchables_counts
    with
    | Not_found -> matchables_counts := MatchableMap.add k 1 !matchables_counts
  ;;

  let with_fresh_vars = ref 0

  let clear_mc () =
    with_fresh_vars := 0;
    matchables_counts := MatchableMap.empty
  ;;

  let report_mc () =
    Format.printf "with fresh = %d\n%!" !with_fresh_vars;
    !matchables_counts
    |> MatchableMap.iter (fun k v ->
           Format.printf "\t%s -> %d\n%!" (GT.show Matchable.ground k) v)
  ;;

  let trie = ref Pats_tree.empty

  (* ******************** Default synthesis shortucts ************************* *)
  let default_shortcut0 m max_height cases rez =
    let open OCanren in
    fresh
      ()
      (debug_var m (flip Matchable.reify) (fun ms ->
           (*        Format.printf "default_shortcut0 on matchable %s\n%!" ((GT.show GT.list) Matchable.show_logic ms);*)
           match ms with
           | [] -> failure
           | _ :: _ :: _ -> failwith "too many answers"
           | [ ms ] ->
             (match Matchable.to_ground ms with
             | None ->
               incr with_fresh_vars;
               success
             | Some m ->
               incr_mc m;
               if Pats_tree.is_set !trie (Matchable.ground_to_list_repr m)
               then success
               else failure)))
      (W.matchable_leq_nat m max_height !!true)
      (cases =/= Std.nil ())
      (rez === MatchableKind.good)
  ;;

  let default_shortcut _etag m _cases history _typs _rez =
    let open OCanren in
    W.not_in_history m history !!true &&& success
  ;;

  let default_shortcut_tag constr_names cases _rez =
    let open OCanren in
    let open OCanren.Std in
    conde
      [ constr_names === nil () &&& failure
      ; fresh u (constr_names === u % nil ()) (cases === nil ())
      ; fresh (u v w) (constr_names === u % (v % w))
      ]
  ;;

  let default_shortcut4 _tag _tag rez =
    let open OCanren in
    let open OCanren.Std in
    rez === !!false
  ;;

  (* ************************************************************************ *)

  (** synthetizer main  *)
  let work
      ?(n = 10)
      ~with_hack
      ~print_examples
      ~check_repeated_ifs:_
      ~debug_filtered_by_size
      ~prunes_period
      ~with_default_shortcuts
    =
    print_endline
      "%%%%%%%%%%%%%%%%%%%%%%%% ALGO WILDCARD \
       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    let printed_clauses = Format.asprintf "%a" Clauses.pretty_print Arg.clauses in
    Format.printf "%s" printed_clauses;
    let max_ifs_count = ref 0 in
    let set_initial_bound () = max_ifs_count := Arg.max_ifs_count in
    set_initial_bound ();
    let __ () =
      match Arg.possible_answer with
      | None -> ()
      | Some a ->
        Format.printf "A priori answer:\n%a\n%!" (GT.fmt IR.ground) a;
        assert (Arg.max_ifs_count <= IR.count_ifs_ground a)
    in
    Format.printf "Initial upper bound of IF-ish constructions = %d\n%!" !max_ifs_count;
    (* Format.printf "\t\tmax_matchable_height = %d\n%!" Arg.max_height; *)
    (* Format.printf "\t\tmax_nested_switches = %d\n%!" Arg.max_nested_switches; *)
    Format.printf
      "\t\tprunes_period = %s\n%!"
      (match prunes_period with
      | Some n -> string_of_int n
      | None -> "always");
    let upgrade_bound x =
      if !max_ifs_count > x
      then (
        let () = Format.printf "Set upper bound of IF-ish constructions to %d\n%!" x in
        max_ifs_count := x)
    in
    let max_height = N.(inject @@ of_int Arg.max_height) in
    (* Raises [FilteredOut] when answer is not worth it *)
    let count_if_constructors
        ?(chk_too_many_cases = true)
        ?(chk_order = false)
        ?(chk_history = false)
        : IR.logic -> int
      =
     fun root ->
      (*
      let next_seen seen scru tag =
        if not check_repeated_ifs
        then seen
        else
            match Matchable.to_ground scru with
            | Some mground ->
                if List.mem mground seen
                then raise FilteredOutByForm
                else if not (Pats_tree.is_set !trie (Matchable.ground_to_list_repr mground))
                then raise FilteredOutByForm
                else mground :: seen
            | _ -> seen
      in
      *)
      let rec helper ~height ~count seen : IR.logic -> _ = function
        | Var (_, _) | Value (Lit _) | Value Fail -> count
        | Value (Switch (_, Value Std.List.Nil, _)) -> raise FilteredOutByForm
        | Value (Switch (scru, xs, on_default)) ->
          let height = height + 1 in
          let max_number_cases, new_seen =
            match Matchable.to_ground scru with
            | Some m ->
              let repr = Matchable.ground_to_list_repr m in
              if not (Pats_tree.is_set !trie repr) then raise FilteredOutByForm;
              let max_cases = Unn_pre.TagSet.cardinal (Pats_tree.find_exn !trie repr) in
              let new_seen =
                if chk_history && List.mem m seen then raise FilteredOutByForm;
                m :: seen
              in
              max_cases, new_seen
            | None -> max_int, seen
          in
          let open Std.List in
          let rec my_fold_list_logic cases_count prev_ground_cstr acc = function
            | Var _ -> acc
            | Value (Cons (Var _, tl)) ->
              let cases_count =
                let cases_count = cases_count + 1 in
                if chk_too_many_cases
                then
                  if cases_count >= max_number_cases then raise FilteredOutByTooManyCases;
                cases_count
              in
              my_fold_list_logic cases_count prev_ground_cstr (acc + 1) tl
            | Value (Cons (Value (c, br), tl)) ->
              let cases_count =
                let cases_count = cases_count + 1 in
                if chk_too_many_cases
                then
                  if cases_count >= max_number_cases then raise FilteredOutByTooManyCases;
                cases_count
              in
              let next_constructor =
                if chk_order
                then (
                  match prev_ground_cstr, c with
                  | None, Var _ -> None
                  | None, Value _ ->
                    let cur_tag = Tag.to_ground_exn c in
                    Some (Tag.to_int cur_tag)
                  | Some _, Var _ -> prev_ground_cstr
                  | Some p, Value _ ->
                    let cur_tag = Tag.to_int @@ Tag.to_ground_exn c in
                    if cur_tag <= p then raise FilteredOutByTagsOrder;
                    Some cur_tag)
                else None
              in
              let acc0 = helper ~height ~count:(acc + 1) new_seen br in
              my_fold_list_logic cases_count next_constructor acc0 tl
            | Value Nil -> acc
          in
          let count_in_cases = my_fold_list_logic 0 None count xs in
          helper ~height ~count:count_in_cases seen on_default
        (*
          GT.foldl Std.List.logic (fun acc -> function
            | Value (Var _, code) -> helper ~height ~count:acc seen code
            | Value (tagl, code) ->
                let seen = next_seen seen scru tagl in
                helper ~height ~count:acc seen code
            | Var _ -> acc)
            0
            xs
          +
          (helper ~height ~count:(count + (logic_list_len_lo xs)) seen on_default)
   *)
      in
      helper ~height:0 ~count:0 [] root
    in
    let _ifs_size_hack (ans : IR.injected) =
      let _do_debug = true in
      let _do_debug = false in
      structural ans IR.reify (fun (ir : IR.logic) ->
          let verbose = true in
          let verbose = false in
          let verbose_exc = true in
          let verbose_exc = false in
          try
            let n =
              count_if_constructors ~chk_too_many_cases:false ~chk_history:false ir
            in
            assert (n >= 0);
            match n with
            | x when x >= !max_ifs_count -> raise (FilteredOutBySize x)
            | _ ->
              (*if verbose then
                  Format.printf "height_hack `%s` = %d\n%!" (IR.show_logic ir) n;*)
              true
          with
          | FilteredOutBySize n ->
            if verbose && verbose_exc && debug_filtered_by_size
            then
              Format.printf
                "  %s (size = %d) \x1b[31mFILTERED OUT\x1b[39;49m because of Ifs count \n\
                 %!"
                (IR.show_logic ir)
                n;
            false
          | FilteredOutByForm ->
            if verbose && verbose_exc && debug_filtered_by_size
            then
              Format.printf
                "  %s \x1b[31mFILTERED OUT\x1b[39;49m because of form \n%!"
                (IR.show_logic ir);
            false
          | FilteredOutByNestedness ->
            if verbose && verbose_exc && debug_filtered_by_size
            then
              Format.printf
                "  %s \x1b[31mFILTERED OUT\x1b[39;49m because by nestedness\n%!"
                (IR.show_logic ir);
            false
          | FilteredOutByTooManyCases ->
            if verbose && verbose_exc && debug_filtered_by_size
            then
              Format.printf
                "  %s \x1b[31mFILTERED OUT\x1b[39;49m because by too many cases\n%!"
                (IR.show_logic ir);
            false
          | FilteredOutByTagsOrder ->
            if verbose && verbose_exc && debug_filtered_by_size
            then
              Format.printf
                "  %s \x1b[31mFILTERED OUT\x1b[39;49m because by tags order\n%!"
                (IR.show_logic ir);
            false)
    in
    (*    let (_: Expr.injected -> Nat.injected -> Typs.injected -> _ -> IR.injected -> _ -> goal) = Work.eval_ir in*)
    (*    let (_: IR.injected -> Expr.injected -> Typs.injected -> IR.injected -> _ -> goal) = my_eval_ir in*)
    let () =
      trie := Arg.minimal_trie;
      Pats_tree.pp Format.std_formatter !trie
    in
    let injected_clauses = Clauses.inject Arg.clauses in
    let injected_typs = Typs.inject Arg.typs in
    let examples : (Expr.injected -> goal) list =
      let goal_of_pattern mode : Expr.injected -> Pattern.ground -> goal =
       fun scru pat ->
        let wcn = Pattern.count_wildcards pat in
        let reconstruct : _ -> Pattern.ground -> _ =
          GT.transform Pattern.ground (fun fself ->
              object (self)
                method c_PConstr acc _ name args =
                  let args2, acc2 = self#rec_list acc args in
                  Expr.constr !!name args2, acc2

                method c_WildCard acc _ = List.hd acc, List.tl acc

                method rec_list acc =
                  function
                  | Std.List.Nil -> Std.nil (), acc
                  | Std.List.Cons (h, tl) ->
                    let h2, acc2 = fself acc h in
                    let tl2, acc3 = self#rec_list acc2 tl in
                    Std.List.cons h2 tl2, acc3
              end)
        in
        let unif, fresh =
          match mode with
          | `Unif -> ( === ), Fresh.one
          | `Diseq -> ( =/= ), OCanren.wc
        in
        (* TODO: constructing wildcards requires only single wilcard.
           Simplify !!! *)
        let rec helper acc n =
          if n <= 0
          then unif scru (fst (reconstruct acc pat))
          else fresh (fun q -> helper (q :: acc) (n - 1))
        in
        helper [] wcn
      in
      let inputs : (Expr.injected -> goal) list =
        let clauses = List.append Arg.clauses [ Pattern.WildCard, IR.Lit 42 ] in
        snd
        @@ List.fold_left
             (fun (diseqs, answers) (p, _) ->
               let diseqs2 = (fun q -> goal_of_pattern `Diseq q p) :: diseqs in
               let answers2 =
                 answers
                 @ [ (fun q ->
                       List.fold_left
                         (fun acc diseq -> acc &&& diseq q)
                         (* (goal_of_pattern `Unif q p) *)
                         success
                         diseqs)
                   ]
               in
               diseqs2, answers2)
             ([], [])
             clauses
      in
      let inputs = List.rev inputs in
      (* let inputs = (fun q -> q === Expr.(pair false_ false_)) :: inputs in
      let inputs =
        [ (fun q -> q === Expr.(pair false_ false_))
          (* ; (fun q -> q === Expr.(pair true_ false_)) *)
          (* ; (fun q -> q === Expr.(pair false_ true_)) *)
          (* ; (fun q -> q === Expr.(pair true_ true_)) *)
        ; (fun q -> fresh x (q === Expr.(pair true_ x))) (* IMPRTANT *)
        ; (fun q ->
            fresh x
              (q === Expr.(pair x true_))
              (wc (fun __ -> q =/= Expr.(pair true_ __))) )
          (* ; (fun q ->
              fresh ()
                (wc (fun __ -> q =/= Expr.(pair __ true_)))
                (wc (fun __ -> q =/= Expr.(pair true_ __))) ) *) ] in *)
      let () =
        if print_examples
        then
          inputs
          |> List.iter (fun example_goal ->
                 let open Tester in
                 runR Expr.reify Expr.show Expr.show_logic (-1) q qh ("", example_goal);
                 let goal_interpret1 rez =
                   fresh
                     scru
                     (example_goal scru)
                     (W.eval_pat scru injected_clauses (Std.Option.some rez))
                 in
                 let __ _ =
                   runR
                     IR.reify
                     IR.show
                     IR.show_logic
                     (-1)
                     q
                     qh
                     ("test example", goal_interpret1);
                   [%tester runR IR.reify IR.show IR.show_logic (-1) (fun q -> success)]
                 in
                 ())
      in
      inputs
    in
    Mybench.set_start_info
      Arg.info
      ~n
      prunes_period
      ~clauses:printed_clauses
      ~examples:(List.length examples);
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
    let info = Format.sprintf "Algo with wildcards (%s)" Arg.info in
    let answer_index = ref (-1) in
    let on_ground ~span ir =
      incr answer_index;
      let nextn = IR.count_ifs_ground ir in
      upgrade_bound nextn;
      let repr = Printf.sprintf "%s with ifs_low=%d" (IR.show ir) nextn in
      Mybench.when_enabled
        ~fail:(fun () -> repr)
        (fun () ->
          Mybench.got_answer span ~idx:!answer_index;
          repr)
    in
    let on_logic ~span ir =
      incr answer_index;
      let nextn = IR.count_ifs_low ir in
      upgrade_bound nextn;
      let repr = Printf.sprintf "%s with ifs_low=%d" (IR.show_logic ir) nextn in
      Mybench.when_enabled
        ~fail:(fun () -> repr)
        (fun () ->
          Mybench.got_answer span ~idx:!answer_index;
          repr)
    in
    let shortcut0 m maxheight cases rez =
      Arg.shortcut0 m maxheight cases rez
      &&&
      if with_default_shortcuts then default_shortcut0 m maxheight cases rez else success
    in
    let shortcut1 etag m cases history typs rez =
      Arg.shortcut etag m cases history rez
      &&&
      if with_default_shortcuts
      then default_shortcut etag m cases history typs rez
      else success
    in
    let shortcut_tag1 constr_names cases rez =
      Arg.shortcut_tag constr_names cases rez
      &&&
      if with_default_shortcuts
      then default_shortcut_tag constr_names cases rez
      else success
    in
    let shortcut4 a b rez =
      if with_default_shortcuts then default_shortcut4 a b rez else success
    in
    let my_eval_ir ideal (s : Expr.injected) tinfo ir rez =
      (if with_hack then _ifs_size_hack ideal else success)
      &&& (* There we use shortcuts optimized for search.
           * These shortcuts canptentially broke execution in default direction
           *)
      W.eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag1 shortcut4 ir rez
    in
    Mybench.repeat (fun () ->
        set_initial_bound ();
        answer_index := -1;
        clear_mc ();
        let start = Mtime_clock.counter () in
        let open Mytester in
        runR
          IR.reify
          on_ground
          on_logic
          n
          q
          qh
          ( info
          , fun ideal_IR ->
              let init = Arg.ir_hint ideal_IR in
              ListLabels.fold_left ~init examples ~f:(fun acc ex ->
                  fresh
                    (res_pat res_ir scru)
                    acc
                    (ex scru)
                    (W.eval_pat scru injected_clauses res_pat)
                    (conde
                       [ fresh
                           n
                           (res_pat === Std.Option.some (IR.int n))
                           (res_ir === Std.Option.some n)
                       ; fresh
                           ()
                           (res_pat === Std.Option.none ())
                           (res_ir === Std.Option.none ())
                       ])
                    (my_eval_ir ideal_IR scru injected_typs ideal_IR res_ir)
                    (debug_var scru (flip Expr.reify) (function
                        | [ scru ] ->
                          (* Format.printf "testing on scrutinee: %s\n%!"
                             (Expr.show_logic scru); *)
                          success
                        | _ -> success))
                    (debug_var ideal_IR (flip IR.reify) (fun irs ->
                         let verbose = false in
                         (*                  let verbose = true in*)
                         let ir =
                           match irs with
                           | [] -> assert false
                           | [ ir ] -> ir
                           | _ -> assert false
                         in
                         let verdict =
                           try
                             let n =
                               count_if_constructors
                                 ~chk_order:true
                                 ~chk_too_many_cases:true
                                 ~chk_history:false
                                 ir
                             in
                             assert (n >= 0);
                             match n with
                             | x when x > !max_ifs_count -> raise (FilteredOutBySize x)
                             | _ ->
                               if verbose
                               then
                                 Format.printf
                                   "height_hack `%s` = %d\n%!"
                                   (IR.show_logic ir)
                                   n;
                               true
                           with
                           | FilteredOutBySize _n -> false
                           | FilteredOutByForm -> false
                           | FilteredOutByNestedness -> false
                           | FilteredOutByTooManyCases -> false
                           | FilteredOutByTagsOrder ->
                             if false
                                (* verbose && verbose_exc && debug_filtered_by_size *)
                             then
                               Format.printf
                                 "  %s \x1b[31mFILTERED OUT\x1b[39;49m because by tags \
                                  order\n\
                                  %!"
                                 (IR.show_logic ir);
                             false
                         in
                         if verdict then success else failure))) );
        let span = Mtime_clock.count start in
        Format.printf "\n";
        Format.printf
          "Total synthesis time: %s\n%!"
          (let ms = Mtime.Span.to_ms span in
           if ms > 10000.0
           then Format.sprintf "%10.0fs \n%!" (Mtime.Span.to_s span)
           else Format.sprintf "%10.0fms\n%!" ms);
        report_mc ());
    let () = disable_periodic_prunes () in
    ()
  ;;

  let test
      ?(print_examples = true)
      ?(debug_filtered_by_size = true)
      ?(with_hack = true)
      ?(check_repeated_ifs = false)
      ?(prunes_period = Some 100)
      ?(with_default_shortcuts = true)
      n
    =
    if !is_enabled
    then
      work
        ~n
        ~with_hack
        ~print_examples
        ~check_repeated_ifs
        ~debug_filtered_by_size
        ~with_default_shortcuts
        ~prunes_period
    else ()
  ;;
end
