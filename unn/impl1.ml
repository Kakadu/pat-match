(* More structural constraints specialized for TwoNilLists
 *
 **)
open Main_inputs
open Unn_pre
open OCanren
open Unn_pre.IR


(* Specialized for two nil lists *)
module Make(Arg: ARG_FINAL) = struct

  let work ?(n=10) clauses typs =
    let max_ifs_count : int = IR.count_ifs_ground Arg.possible_answer in
    Format.printf "max IFs count = %d\n%!" max_ifs_count;

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
    let do_debug = false in

    let prev = ref (Obj.magic false) in
    structural ans IR.reify (fun ir ->
      let verbose = not (!prev = ir) in
      prev := ir;
(*      Format.printf "verbose = %b\n%!" verbose;*)
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


    let hack ideal goal =
      (height_hack ideal) &&&
      goal
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
      let n = if n < 3 then 3 else n in
      if has_var
      then OCanren.CAtLeast n
      else OCanren.CFixed n
    in*)


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

    (* this is bad *)
    let rec list_nth_nat idx xs q114 =
      let open Unn_pre.Nat in
      let open Unn_pre.Matchable in

      let (%) = Std.(%) in
      let pair = Std.Pair.pair in
      fresh (q115)
        (q115 === (Std.Pair.pair idx xs))
        (conde
          [ (fresh (x q116)
            (q115 === (Std.Pair.pair (z) (x % q116)))
              (x === q114))
          ; (fresh (n q118 xs)
                (q115 === (pair (s n) (q118 % xs)))
                (list_nth_nat n xs q114))
          ])
    in

    let rec my_eval_m sc h ans =
      let open Unn_pre.Nat in
      let open Unn_pre.Matchable in
      conde
        [ fresh (a b)
            (h === (scru ()))
            (sc === ans)
            ((Expr.constr !!"pair" Std.(a %< b) === ans))
        ; fresh (n m q23 cname es)
            (* field of scrutineee *)
            (scru () === m)
            (h === (field n m))
            (conde [  n === (s z); n === z ])
            (q23 === (Expr.constr cname es))
            (list_nth_nat n es ans)
            (my_eval_m sc m q23)

        ; fresh (n m q23 q24 es)
            (h === (field n m))
            (m =/= scru())
            (conde [ n === z; n === (Nat.s z) ])
            (q23 === (Expr.constr q24 es))
            (list_nth_nat n es ans)
            (my_eval_m sc m q23)
        ]
    in

    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->
      (*
        Format.printf "structural of '%s' with cname=%a and scru = %s\n"
          (IR.show_logic ir)
          (GT.fmt GT.string) cname
          (Matchable.show scru);
          *)
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

(*        Format.printf "structural of '%s' with cname=%a and scru = %s\n"
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

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s ir ans =

        let make_constraints_goal tag ~th ~el scru2 =
          let open Matchable in
          let wrap tag_str scur_g =
             (make_constraint th scur_g tag_str) &&&
             (make_constraint el scur_g tag_str)
          in
          conde
            [ (scru2 === scru   ()) &&& failure
            ; (scru2 === field0 ())
              &&& (conde
                    [ tag === !!"nil"  &&& (wrap "nil"  (Field (Z,Scru)) )
                    ; tag === !!"nil2" &&& (wrap "nil2" (Field (Z,Scru)) )
                    ; tag === !!"cons" &&& (wrap "cons" (Field (Z,Scru)) )
                    ])
              (*&&& (make_constraint2 el (Field (Z,Scru)) )
              &&& (make_constraint2 th (Field (Z,Scru)) )*)

            ; (scru2 === field1 ())
              &&& (conde
                    [ tag === !!"nil"  &&& (wrap "nil"  (Field (S Z,Scru)) )
                    ; tag === !!"nil2" &&& (wrap "nil2" (Field (S Z,Scru)) )
                    ; tag === !!"cons" &&& (wrap "cons" (Field (S Z,Scru)) )
                    ])
              (*&&& (make_constraint2 el (Field (S Z,Scru)))
              &&& (make_constraint2 th (Field (S Z,Scru)))*)

            ; (scru2 === field00()) &&& failure
            ; (scru2 === field01()) &&& failure
            ; (scru2 === field10()) &&& failure
            ; (scru2 === field11()) &&& failure
            ]
        in

        let open Unn_pre.IR in
        conde
          [ (ir === (fail ())) &&& (ans === (none ()))
          ; fresh (n)
              (ir === (int n))
              (ans === (some n))

          ; fresh (tag scru2 th el q14 tag2 args q16 q6)
              (ir === (iftag tag scru2 th el))
              (q14 === (Expr.constr tag2 args))
              (conde
                [ scru2 === Matchable.field0 ()
                ; scru2 === Matchable.field1 ()
(*                ; scru2 === Matchable.field01 ()
                ; scru2 === Matchable.field11 ()
                ; scru2 === Matchable.field10 ()
                ; scru2 === Matchable.field00 ()*)
(*                ; scru2 === Matchable.field000 ()
                ; scru2 === Matchable.field001 ()
                ; scru2 === Matchable.field010 ()
                ; scru2 === Matchable.field011 ()
                ; scru2 === Matchable.field100 ()
                ; scru2 === Matchable.field101 ()
                ; scru2 === Matchable.field110 ()
                ; scru2 === Matchable.field111 ()*)
                ])

              (my_eval_m s scru2 q14)

(*              (conde [tag === !!"cons"; tag === !!"nil"; tag === !!"nil2" ])*)
              (conde
                 [ (tag2 === tag) &&&
                 (*
                   (make_constraints_goal ~th ~el tag scru2) &&&    (* with these constraints it works 85s *)
                   *)
                   (self s th ans)
                 ; (tag2 =/= tag) &&&
                 (*
                   (make_constraints_goal ~th ~el tag scru2) &&&
                   *)
                   (self s el ans)
                 ])
          ]
      in
      (fun a b c ->
        (height_hack ideal) &&&
        (Tabling.(tabledrec three) inner a b c)
      )
    in

    let injected_pats = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        run one (Arg.inhabit Arg.max_height)
          (fun r -> r#prjc Arg.prjp)
        |> OCanren.Stream.take ~n:(-1)
        |> Arg.wrap_demo
      in

      let () =
        demo_exprs |> List.iter (fun e ->
(*          Format.printf "%s --> %!" (Expr.show e);*)
          let open OCanren in
          run one (fun ir ->
              let answer_demo = IR.inject Arg.possible_answer in
              let scru_demo = Expr.inject e in
              fresh (n rez)
                (Work.eval_pat scru_demo injected_pats rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (my_eval_ir answer_demo scru_demo answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  (*
                  Format.printf "%s\n%!"
                    (IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify));*)
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

(*
    let injected_exprs = List.rev injected_exprs in
*)

    Helper.show_local_time ();
    let info = Printf.sprintf "Specd for 2nil (%s)" Arg.info in
    let open Mytester in
    runR IR.reify IR.show IR.show_logic n
      q qh (info, (fun ideal_IR ->
        let init = success in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (Work.eval_pat scru injected_pats res_pat)

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
    Format.printf "\n\n\n%!"


  let test () = work ~n:(2) Arg.clauses Arg.typs

end
