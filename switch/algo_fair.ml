(* Executes exactly what is written in lozovML
 *
 *)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR



let disable_periodic_prunes () =
  let open OCanren.PrunesControl in
  enable_skips ~on:false


exception FilteredOutBySize of int
exception FilteredOutByForm
exception FilteredOutByUnsat
exception FilteredOutByTooManyCases
exception FilteredOutByNestedness
exception Unsat

let is_enabled = ref true


module Make(W: WORK)(Arg: ARG_FINAL) = struct

  module MatchableMap = Map.Make(struct
    type t = Matchable.ground
    let compare x y =
(*      Format.printf "\t%a\n\t%a\n%!" (GT.fmt Matchable.ground) x  (GT.fmt Matchable.ground) y;*)
      let ans = Matchable.ground.plugins#compare x y in
      GT.cmp_to_int ans
  end)
  let matchables_counts : int MatchableMap.t ref = ref MatchableMap.empty
  let incr_mc k =
    try let n = MatchableMap.find k !matchables_counts in
        matchables_counts := (MatchableMap.add k (n+1) !matchables_counts)
    with Not_found ->
        matchables_counts := (MatchableMap.add k 1 !matchables_counts)

  let with_fresh_vars = ref 0
  let clear_mc () =
    with_fresh_vars := 0;
    matchables_counts := MatchableMap.empty

  let report_mc () =
    Format.printf "with fresh = %d\n%!" !with_fresh_vars;
    !matchables_counts |> MatchableMap.iter (fun k v ->
      Format.printf "\t%s -> %d\n%!" (GT.show Matchable.ground k) v
    )

  let trie = ref Pats_tree.empty


  (* ******************** Default synthesis shortucts ************************* *)
  let default_shortcut0 m max_height cases rez =
    let open OCanren in
    fresh ()
      (debug_var m (flip Matchable.reify) (fun ms ->
(*        Format.printf "default_shortcut0 on matchable %s\n%!" ((GT.show GT.list) Matchable.show_logic ms);*)
        match ms with
        | [] -> failure
        | _::_::_ -> failwith "too many answers"
        | [ms] ->
            match Matchable.to_ground ms with
              | None -> incr with_fresh_vars; success
              | Some m ->
                incr_mc m;
                if Pats_tree.is_set !trie (Matchable.ground_to_list_repr m)
                then success
                else failure
      ))
      (W.matchable_leq_nat m max_height !!true)
      (cases =/= Std.nil())
      (rez === !!true)

  let default_shortcut etag m cases history rez =
    let open OCanren in
    (W.not_in_history m history !!true)

  let default_shortcut_tag constr_names cases rez =
    let open OCanren in
    let open OCanren.Std in
    (conde
      [ (constr_names === nil()) &&& failure
      ; fresh (u)
          (constr_names === u % (nil()))
          (cases === nil())
      ; fresh (u v w)
          (constr_names === u % (v % w) )
      ])

  (* ************************************************************************ *)
  (** synthetizer main  *)
  let work ?(n=10) ~with_hack ~print_examples ~check_repeated_ifs ~debug_filtered_by_size
          ~prunes_period ~with_default_shortcuts =
    print_endline "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";

    let printed_clauses = Format.asprintf "%a" Clauses.pretty_print Arg.clauses in
    Format.printf "%s" printed_clauses;
    let max_ifs_count = ref 0 in
    let set_initial_bound () = max_ifs_count := Arg.max_ifs_count in
    set_initial_bound ();

    let () =
      match Arg.possible_answer with
      | None -> ()
      | Some a ->
          Format.printf "A priori answer:\n%a\n%!" (GT.fmt IR.ground) a;
          assert (Arg.max_ifs_count <= (IR.count_ifs_ground a))
    in
    Format.printf "Initial upper bound of IF-ish constructions = %d\n%!" !max_ifs_count;
    Format.printf "\t\tmax_matchable_height = %d\n%!" Arg.max_height;
    Format.printf "\t\tmax_nested_switches = %d\n%!" Arg.max_nested_switches;
    Format.printf "\t\tprunes_period = %s\n%!"
      (match prunes_period with
      | Some n -> string_of_int n
      | None -> "always");

    let upgrade_bound x =
      if !max_ifs_count > x
      then
        let () = Format.printf "Set upper bound of IF-ish constructions to %d\n%!" x in
        max_ifs_count := x
    in

    let () =
        trie := Pats_tree.build Arg.clauses Arg.typs;
        trie := Pats_tree.remove !trie [];
        Pats_tree.pp Format.std_formatter !trie
    in
    let max_height = N.(inject @@ of_int Arg.max_height) in

    (** Raises [FilteredOut] when answer is not worth it *)
    let count_if_constructors ~check_repeated_ifs init_g folder : IR.logic -> _ * int = fun root ->
      let next_seen seen scru tag =
        if not check_repeated_ifs
        then seen
        else
            match Matchable.to_ground scru with
            | Some mground ->
                if List.mem mground seen
                then raise FilteredOutByForm
                else
(*                  let () = Format.printf "looking for matchable %a\n%!" (GT.fmt Matchable.ground) mground in*)
                  if not (Pats_tree.is_set !trie (Matchable.ground_to_list_repr mground))
                  then raise FilteredOutByForm
                  else mground :: seen
            | _ -> seen
      in
      let rec helper ~height ~count seen goal_acc = function
      | Var (_,_)
      | Value (Lit _)
      | Value Fail -> (goal_acc,count)
      | Value (Switch (_, Value Std.List.Nil, _)) -> raise FilteredOutByForm
      | Value (Switch (scru, xs, on_default)) ->
          let height = height + 1 in
          let () =
            if height > Arg.max_nested_switches
            then raise FilteredOutByNestedness
          in
          let seen = next_seen seen scru scru in
          let goal_acc = folder goal_acc scru xs in
          let goal_acc,count =
            (helper ~height ~count:(count + (logic_list_len_lo xs)) seen goal_acc on_default)
          in
          GT.foldl Std.List.logic (fun ((acc_g,count) as acc) -> function
            | Value (Var (n,cstr), code) ->
                (*let () =
                  match cstr with
                  | [] -> ()
                  | _ -> Format.printf "\t\t\x1b[33mVar %d has %d constraints\x1b[39;49m\n%!" n (List.length cstr)
                in*)
                helper ~height ~count seen goal_acc code
            | Value (tagl, code) ->

                helper ~height ~count seen goal_acc code
            | Var _ -> acc)
            (goal_acc,count)
            xs


      in
      helper ~height:0 ~count:0 [] init_g root
    in

    let _ifs_size_hack (ans: IR.injected) =
      let _do_debug = true in
      let _do_debug = false in

      structural ans IR.reify (fun (ir: IR.logic) ->
        let verbose = true in
        let verbose = false in
        let debug fmt =
          Format.ksprintf (fun s -> if _do_debug&&verbose then Format.printf "%s" s else ())
            fmt
        in
        try
          if verbose then
            Format.printf "height_hack `%s` = %!" (IR.show_logic ir);
          let ((),n) = count_if_constructors ~check_repeated_ifs:false () (fun () _ _ -> ()) ir in
          assert (n >= 0);
          if verbose then
            Format.printf "\x1b[32m%d\x1b[39;49m%!" n;
          match n with
          | x when x > !max_ifs_count ->
            raise (FilteredOutBySize x)
          | _ ->
              if verbose then
                Format.printf "\n%!";
              true
        with
          | FilteredOutBySize n ->
            if debug_filtered_by_size
            then Format.printf "  %s (size = %d) \x1b[31mFILTERED OUT\x1b[39;49m because of Ifs count \n%!"
              (IR.show_logic ir) n ;
            false
          | FilteredOutByForm ->
            if debug_filtered_by_size
            then Format.printf "  %s \x1b[31mFILTERED OUT\x1b[39;49m because of form \n%!"
                (IR.show_logic ir) ;
            false
          | FilteredOutByNestedness ->
            if debug_filtered_by_size
            then Format.printf "  %s \x1b[31mFILTERED OUT\x1b[39;49m because by nestedness\n%!"
                (IR.show_logic ir) ;
            false

      )
    in

(*    let (_: Expr.injected -> Nat.injected -> Typs.injected -> _ -> IR.injected -> _ -> goal) = Work.eval_ir in*)
(*    let (_: IR.injected -> Expr.injected -> Typs.injected -> IR.injected -> _ -> goal) = my_eval_ir in*)



    let injected_clauses = Clauses.inject Arg.clauses in
    let injected_typs = Typs.inject Arg.typs in
    let injected_exprs =
      let demo_exprs =
        run one (fun q -> Arg.inhabit Arg.max_height q) (fun r -> r#prjc Expr.prjc)
        |> OCanren.Stream.take ~n:(-1)
      in

      let () =
        if print_examples
        then Format.printf "Testing %d examples:\n%!" (List.length demo_exprs);

        demo_exprs |> List.iter (fun e ->
          if print_examples then Format.printf "  %s ~~> %!" (Expr.show e);
          match Arg.possible_answer with
          | None -> Format.printf "?\n%!"
          | Some ans ->
              let answer_demo = IR.inject ans in
              let scru_demo = Expr.inject e in
              let stream =
                OCanren.(run one) (fun ir ->
                  fresh (n rez)
                    (W.eval_pat scru_demo injected_clauses rez)
                    (rez === Std.Option.some ir)
                    (ir === IR.int n)
                    (W.eval_ir scru_demo max_height injected_typs simple_shortcut0 simple_shortcut simple_shortcut_tag answer_demo (Std.Option.some n))
                )
                (fun r -> r)
              in

              let () =
                if OCanren.Stream.is_empty stream
                then(*
                  let () =
                    let open Mytester in
                    runR (Std.Option.reify OCanren.reify)
                      (fun ~span:_ -> GT.show Std.Option.ground @@ GT.show GT.int)
                      (fun ~span:_ -> GT.show Std.Option.logic (GT.show logic @@ GT.show GT.int))
                      1 q qh
                      ("eval_ir", (Work.eval_ir scru_demo max_height typs simple_shortcut0 simple_shortcut simple_shortcut_tag answer_demo))
                  in
                  *)
                  failwith "Bad (?) example"
              in
              if print_examples
              then Format.printf "%s\n%!" @@
                    IR.show_logic ((OCanren.Stream.hd stream)#reify IR.reify);

          )
      in
      List.map Expr.inject demo_exprs
    in

    Mybench.set_start_info Arg.info ~n prunes_period ~clauses:printed_clauses ~examples:(List.length injected_exprs);

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
    let info = Format.sprintf "fair lozovML (%s)" Arg.info in



    let answer_index = ref (-1) in
    let on_ground ~span ir =
      incr answer_index;
      let nextn = IR.count_ifs_ground ir in
      upgrade_bound nextn;
      let repr = Printf.sprintf "%s with ifs_low=%d" (IR.show ir) nextn in
      Mybench.when_enabled ~fail:(fun () -> repr)
        (fun () ->
          Mybench.got_answer span ~idx:(!answer_index);
          repr)
    in
    let on_logic ~span ir =
      incr answer_index;
      let nextn = IR.count_ifs_low ir in
      upgrade_bound nextn;
      let repr = Printf.sprintf "%s with ifs_low=%d" (IR.show_logic ir) nextn in
      Mybench.when_enabled ~fail:(fun () -> repr)
        (fun () ->
          Mybench.got_answer span ~idx:(!answer_index);
          repr)
    in

    let shortcut0 m maxheight cases rez =
      (Arg.shortcut0 m maxheight cases rez) &&&
      (if with_default_shortcuts
       then default_shortcut0 m maxheight cases rez
       else success)
    in
    let shortcut1 etag m cases history rez =
      (Arg.shortcut etag m cases history rez) &&&
      (if with_default_shortcuts
       then default_shortcut etag m cases history rez
       else success)
    in
    let shortcut_tag1 constr_names cases rez =
      (Arg.shortcut_tag constr_names cases rez) &&&
      (if with_default_shortcuts
       then default_shortcut_tag constr_names cases rez
       else success)
    in
    let my_eval_ir ideal (s: Expr.injected) tinfo ir rez =
      (if with_hack then _ifs_size_hack ideal else success) &&&
      (* There we use shortcuts optimized for search.
       * These shortcuts canptentially broke execution in default direction
       *)
      (W.eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag1 ir rez)
    in


    let my_satisfiability acc scrul (xs: (Tag.logic * _) OCanren.logic Std.List.logic) =
      (* check single switch case *)
      let check_single acc m tag_names = function
        | Value _ -> acc
        | Var (_,cstrs) ->
            let open Unn_pre in

            if List.length cstrs < TagSet.cardinal tag_names - 1
            then acc
            else
              (* we need to try to exclude possible constructors to get a verdict *)
              let survieved_tags =
                ListLabels.fold_left ~init:tag_names cstrs ~f:(fun acc tagl ->
                  match Tag.to_ground tagl with
                  | None ->
                      (* less chances to deduce something interesting *)
                      acc
                  | Some tag when not (TagSet.mem tag acc) ->
                      failwith "should not happen. Probably we already removed that tag"
                  | Some tag -> TagSet.remove tag acc
                )
              in
              match TagSet.cardinal survieved_tags with
              | card when card <= 0 -> raise FilteredOutByUnsat
(*              | 1 -> (Tag.inject (TagSet.min_elt survieved_tags) === *)
              | _ -> acc
      in
      match Matchable.to_ground scrul with
      | None -> acc
      | Some m ->
          try
            let tag_names = Pats_tree.find_exn !trie (Matchable.ground_to_list_repr m) in
            let card = TagSet.cardinal tag_names in
            let rec my_fold_list_logic count acc = function
              | Var _ -> acc
              | Value (Std.List.Cons (Var _, tl))
              | Value (Std.List.Cons (Value (Value _,_), tl)) ->
                  let count = count + 1 in
                  if count >= card then raise FilteredOutByTooManyCases;
                  my_fold_list_logic count acc tl
              | Value (Cons (Value (Var (_,_) as case, _), tl)) ->
                  let count = count + 1 in
                  if count >= card then raise FilteredOutByTooManyCases;
                  let acc = check_single acc m tag_names case in
                  my_fold_list_logic count acc  tl
              | Value Nil -> acc
            in
            my_fold_list_logic 0 acc xs
            (*
            GT.foldl Std.List.logic (fun (len,acc) p ->
              let len = len+1 in
              if len >= card then raise Unsat;
              match p with
              | Var _ -> (len,acc)
              | Value (Value _,_) ->
                  (* we dont' check cases known to be ground *)
                  (len,acc)
              | Value (Var (_,_) as case,_) -> (len,check_single acc m tag_names case)
            )
            (0,acc)
            xs
            |> snd
            *)
          with Unsat -> failure
             | Not_found ->
(*                Format.printf "Can't find info for matchable %a\n%!" (GT.fmt Matchable.ground) m;*)
                failure
    in

    Mybench.repeat begin fun () ->
      set_initial_bound ();
      answer_index := -1;
      clear_mc ();
      let start = Mtime_clock.counter () in
      let open Mytester in
      runR IR.reify on_ground on_logic n q qh (info, (fun ideal_IR ->
          let init = Arg.ir_hint ideal_IR in

          List.fold_left (fun acc (scru: Expr.injected) ->
            fresh (res_pat res_ir)
              acc
              (W.eval_pat             scru injected_clauses res_pat)
              (conde
                [ fresh (n)
                    (res_pat === Std.Option.some (IR.int n))
                    (res_ir  === Std.Option.some n)
                ; fresh ()
                    (res_pat === Std.Option.none ())
                    (res_ir === Std.Option.none())
                ])
                (my_eval_ir  ideal_IR scru injected_typs ideal_IR res_ir)
                (debug_var ideal_IR (flip IR.reify) (fun irs ->
                  let ir =
                    match irs with
                    | [] -> assert false
                    | [ir] -> ir
                    | _ -> assert false
                  in
                  let _verbose_exc = true in
                  let _verbose_exc = false in
                  let verbose = true in
                  let verbose = false in
(*                  let debug fmt =
                    Format.ksprintf (fun s -> if verbose then Format.printf "%s" s else ())
                      fmt
                  in*)
                  let verdict =
                    try
                      (*if verbose then
                        Format.printf "after_hack `%s` = %!" (IR.show_logic ir);*)
                      let (hack,n) = count_if_constructors ~check_repeated_ifs:true success my_satisfiability ir in
                      assert (n >= 0);
                      match n with
                      | x when x > !max_ifs_count ->
                        raise (FilteredOutBySize x)
                      | _ ->
                          if verbose then
                            Format.printf "after_hack `%s` = \x1b[32m%d\x1b[39;49m\n%!" (IR.show_logic ir) n;

                          (*if verbose then
                            Format.printf "\n%!";*)
                          Some hack
                    with
                      | FilteredOutBySize n ->
                        if verbose && _verbose_exc then begin
                          Format.printf "after_hack `%s` (size = %d) \x1b[31mFILTERED OUT\x1b[39;49m because of Ifs count \n%!"
                            (IR.show_logic ir) n
                        end;
                        None
                      | FilteredOutByForm ->
                          if verbose && _verbose_exc then begin
                            Format.printf "after_hack `%s` \x1b[31mFILTERED OUT\x1b[39;49m because of form \n%!"
                              (IR.show_logic ir)
                          end;
                          None
                      | FilteredOutByTooManyCases ->
                          if verbose && _verbose_exc then begin
                            Format.printf "after_hack `%s` \x1b[31mFILTERED OUT\x1b[39;49m by too many cases\n%!"
                              (IR.show_logic ir)
                          end;
                          None
                      | FilteredOutByNestedness ->
                          if verbose && _verbose_exc then
                            Format.printf "after_hack `%s` \x1b[31mFILTERED OUT\x1b[39;49m by nestedness\n%!"
                              (IR.show_logic ir)
                          ;
                          None
                      | FilteredOutByUnsat ->
                          if verbose && _verbose_exc then
                            Format.printf "after_hack `%s` \x0b[36mFILTERED OUT\x1b[39;49m by unsat\n%!"
                              (IR.show_logic ir)
                          ;
                          None
                  in
                  match verdict with
                  | Some g -> g
                  | None -> failure
                ))
            )
            init
            injected_exprs
        ));
      let span = Mtime_clock.count start in


      Format.printf "\n";
      Format.printf "Total synthesis time: %s\n%!"
        ( let ms = Mtime.Span.to_ms span in
          if ms > 10000.0
          then Format.sprintf "%10.0fs \n%!" (Mtime.Span.to_s span)
          else Format.sprintf "%10.0fms\n%!" ms);
      report_mc ();
  end;
  let () = disable_periodic_prunes () in
  ()

  let test ?(print_examples=true) ?(debug_filtered_by_size=false)
      ?(with_hack=true) ?(check_repeated_ifs=true)
      ?(prunes_period=(Some 100)) ?(with_default_shortcuts=true)
      n =
    if !is_enabled
    then work ~n ~with_hack ~print_examples ~check_repeated_ifs
      ~debug_filtered_by_size ~with_default_shortcuts
      ~prunes_period
    else ()
end


