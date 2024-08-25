(* let%expect_test _ =
   let open Unn_pre in
   let clauses = [ (ptrue, IR.eint 1); (pfalse, IR.eint 0) ] in

   let injected : Clauses.injected = Clauses.inject clauses in
   let ans =
     OCanren.(run q (Work_base_common.compile_naively injected)) (fun rr ->
         rr#reify IR.prj_exn)
     |> OCanren.Stream.hd
   in
   print_endline (GT.show IR.ground ans);
   [%expect {||}] *)

let trace_pats ps =
  let open OCanren in
  debug_var ps (Std.List.prj_exn Unn_pre.Pattern.prj_exn) (function
    | [ ps ] ->
        print_endline "HERR";
        Format.printf "@[[%s]@]@ %!"
          (String.concat " " @@ List.map Unn_pre.Pattern.show ps);
        success
    | _ -> assert false)

let%expect_test _ =
  let open Unn_pre in
  let clauses =
    [
      (ppair ptrue __, IR.eint 1);
      (ppair __ ptrue, IR.eint 1);
      (ppair pfalse pfalse, IR.eint 0);
    ]
  in
  let injected : Clauses.injected = Clauses.inject clauses in
  let ans =
    OCanren.(run q) (Work_base_common.compile_naively injected) (fun rr ->
        rr#reify IR.prj_exn)
    |> OCanren.Stream.hd
  in
  print_endline (GT.show IR.ground ans);
  [%expect
    {| (match S with  | pair -> (match S[0] with  | true -> 1   | _ -> (match S with  | pair -> (match S[1] with  | true -> 1   | _ -> (match S with  | pair -> (match S[1] with  | false -> (match S[0] with  | false -> 0   | _ -> fail)  | _ -> fail)  | _ -> fail))  | _ -> (match S with  | pair -> (match S[1] with  | false -> (match S[0] with  | false -> 0   | _ -> fail)  | _ -> fail)  | _ -> fail)))  | _ -> (match S with  | pair -> (match S[1] with  | true -> 1   | _ -> (match S with  | pair -> (match S[1] with  | false -> (match S[0] with  | false -> 0   | _ -> fail)  | _ -> fail)  | _ -> fail))  | _ -> (match S with  | pair -> (match S[1] with  | false -> (match S[0] with  | false -> 0   | _ -> fail)  | _ -> fail)  | _ -> fail))) |}]

let traco file line =
  let open OCanren in
  debug_var !!1 OCanren.reify (fun _ ->
      Printf.printf "%s %d\n" file line;
      success)
(*
let%expect_test _ =
  let open OCanren in
  let list_mapi f =
    let rec helper i xs q18 =
      conde
        [
          fresh () (traco __FILE__ __LINE__)
            (xs === Std.List.nil ())
            (traco __FILE__ __LINE__)
            (q18 === Std.nil ())
            (traco __FILE__ __LINE__);
          fresh (x q20 q21 q22) (traco __FILE__ __LINE__)
            (xs === Std.List.cons x q20)
            (traco __FILE__ __LINE__)
            (q18 === Std.List.cons q21 q22)
            (f i x q21)
            (helper (Std.Nat.succ i) q20 q22);
        ]
    in
    fun xs q24 -> traco __FILE__ __LINE__ &&& helper Std.Nat.zero xs q24
  in
  let injected : int ilogic Std.List.injected = OCanren.Std.list ( !! ) [ 1 ] in
  let _ =
    OCanren.(run q)
      (list_mapi
         (fun i x q17 -> traco __FILE__ __LINE__ &&& (i === q17))
         injected)
      (fun rr -> rr#reify (Std.List.reify OCanren.reify))
    |> OCanren.Stream.hd
  in
  ();
  [%expect {||}] *)
