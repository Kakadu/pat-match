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


(* ******************** Default synthesis shortucts ************************* *)
let default_shortcut0 m max_height cases rez =
  let open OCanren in
  (Work.matchable_leq_nat m max_height !!true) &&&
  (cases =/= Std.nil()) &&&
  (rez === !!true)

let default_shortcut etag m cases history rez =
  let open OCanren in
  (Work.not_in_history m history !!true)

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


exception FilteredOutBySize of int
exception FilteredOutByForm
exception FilteredOutByNestedness

let is_enabled = ref true

module Make(Arg: ARG_FINAL) = struct
  let work ?(n=10) ~with_hack ~print_examples ~check_repeated_ifs ~debug_filtered_by_size
          ~prunes_period ~with_default_shortcuts clauses typs =
    print_endline "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";

    let printed_clauses = Format.asprintf "%a" Clauses.pretty_print clauses in
    Format.printf "%s" printed_clauses;
    Mybench.set_start_info Arg.info ~n prunes_period ~clauses:printed_clauses;


    let possible_answer = Arg.possible_answer in
    assert (Arg.max_ifs_count <= (IR.count_ifs_ground possible_answer));
    let max_ifs_count = ref Arg.max_ifs_count in
    Format.printf "A priori answer:\n%a\n%!" (GT.fmt IR.ground) possible_answer;
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


    let max_height = N.(inject @@ of_int Arg.max_height) in

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
      let rec helper ~height ~count seen = function
      | Var (_,_)
      | Value (Lit _)
      | Value Fail -> count
      | Value (Switch (_, Value Std.List.Nil, _)) -> raise FilteredOutByForm
      | Value (Switch (scru, xs, on_default)) ->
          let height = height + 1 in
          let () =
            if height > Arg.max_nested_switches
            then raise FilteredOutByNestedness
          in
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
      in
      helper ~height:0 ~count:0 [] root
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

    let rec ground_append xs ys =
      match xs with
      | Std.List.Cons (x, xs) -> Std.List.Cons (x, ground_append xs ys)
      | Std.List.Nil -> ys
    in
    let rec ground_concat xs =
      match xs with
      | Std.List.Nil -> Std.List.Nil
      | Std.List.Cons (xs, tl) -> ground_append xs (ground_concat tl)
    in


    let rec cartesian (xss : 'a Std.List.ground Std.List.ground) =
      match xss with
      | Std.List.Nil -> Std.List.Nil
      | Std.List.Cons (x, xs) ->
          let rest = cartesian xs in
          ground_concat @@
          GT.gmap Std.List.ground
            (fun k -> GT.gmap Std.List.ground (fun xs -> Std.List.Cons(k,xs)) rest) x
    in

    let injected_clauses = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        run one (fun q -> Arg.inhabit Arg.max_height q) (fun r -> r#prjc Expr.prjc )
        |> OCanren.Stream.take ~n:(-1)
      in

      let extra_exprs =
        let rec helper (h: int) (pat: Pattern.ground) : Expr.ground Std.List.ground =
          match pat with
          | Pattern.WildCard -> Std.List.Nil
          | PConstr (name, ps) ->
              let notbad (q: Expr.injected) =
                match ps with
                | Std.List.Nil -> (q =/= (Expr.constr (Tag.inject name) (Std.nil())))
                | Std.List.Cons (_, Std.List.Nil) -> Fresh.one (fun x -> q =/= Std.(Expr.constr Tag.(inject name) !<x))
                | _ -> assert false
              in
              let new_examples =
                run q (fun (q: Expr.injected) -> (notbad q) &&& (Arg.inhabit h q))
                  (fun r -> r#prjc Expr.prjc)
                |> OCanren.Stream.take ~n:(-1)
                |> Std.List.of_list id
              in
              let ps_awsers =
                GT.gmap Std.List.ground (helper (h-1)) ps
                |> cartesian
                |> GT.gmap Std.List.ground (fun xs -> Expr.EConstr (name, xs))
              in
              ground_append ps_awsers new_examples
        in
        List.concat @@
        List.map (fun (p,_) -> helper 3 p |> Std.List.to_list id) clauses
      in

      let all_exprs = demo_exprs in
(*      let all_exprs = demo_exprs @ extra_exprs in*)
      let all_exprs =
          Base.List.dedup_and_sort
            ~compare:(fun a b ->
              match GT.compare Expr.ground a b with
                | GT.LT -> -1
                | GT.EQ -> 0
                | GT.GT -> 1)
            all_exprs
      in
      let all_exprs = Base.List.sort ~compare:(fun a b -> compare (Expr.height a) (Expr.height b)) all_exprs
      in
      let () =
        if print_examples
        then Format.printf "Testing %d examples:\n%!" (List.length all_exprs);


        all_exprs |> List.iter (fun e ->
          if print_examples then Format.printf "  %s -> %!" (Expr.show e);


          let answer_demo = IR.inject possible_answer in
          let scru_demo = Expr.inject e in
          let open OCanren in
          run one (fun ir ->
              fresh (n rez)
                (Work.eval_pat scru_demo injected_clauses rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (Work.eval_ir scru_demo max_height typs simple_shortcut0 simple_shortcut simple_shortcut_tag answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  let () =
                    if OCanren.Stream.is_empty s
                    then
                      let () =
                        let open Mytester in
                        runR (Std.Option.reify OCanren.reify)
                          (fun ~span:_ -> GT.show Std.Option.ground @@ GT.show GT.int)
                          (fun ~span:_ -> GT.show Std.Option.logic (GT.show logic @@ GT.show GT.int))
                          1 q qh
                          ("eval_ir", (Work.eval_ir scru_demo max_height typs simple_shortcut0 simple_shortcut simple_shortcut_tag answer_demo))
                      in
                      failwith "Bad (?) example"
                  in
                  if print_examples
                  then Format.printf "%s\n%!" @@
                        IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify);
            )

          )
      in

      List.map Expr.inject all_exprs
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
      (Work.eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag1 ir rez)
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
      ?(prunes_period=(Some 100)) ?(with_default_shortcuts=true)
      n =
    if !is_enabled
    then work ~n ~with_hack ~print_examples ~check_repeated_ifs
      ~debug_filtered_by_size ~with_default_shortcuts
      ~prunes_period
      Arg.clauses Arg.typs
    else ()
end

