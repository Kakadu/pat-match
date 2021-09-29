open Unn_pre
open Main_inputs.TypsHighlevel

let run (module Arg : Main_inputs.ARG0) =
  let highlevel_typs =
    match Arg.typs_highlevel with
    | Some t -> t
    | None -> failwith "Highlevel types are not implemented for that case"
  in
  let filename = "/tmp/pm.smt2" in
  let ch = open_out filename in
  let ppf = Format.formatter_of_out_channel ch in
  let println fmt = Format.kasprintf (Format.fprintf ppf "%s\n%!") fmt in
  println "(set-logic UFDTLIA)";
  let () =
    let onadt env ~tname:_ ppf =
      List.iter (function cname, args ->
          Format.fprintf ppf " (%s " cname;
          args
          |> List.iter (fun (acc, argname) ->
                 let argname =
                   match List.assoc argname env with
                   | exception Not_found -> argname
                   | s -> s
                 in
                 let argname = if argname = "int" then "Int" else argname in
                 let accessor =
                   match acc with
                   | Some acc -> acc
                   | None ->
                     failwiths
                       "Accessor in the constructor %s (argname %s) is not specified"
                       cname
                       argname
                 in
                 let () = () in
                 Format.fprintf ppf " (%s %s)" accessor argname);
          Format.fprintf ppf ")")
    in
    let env = fst highlevel_typs in
    env
    |> List.iter (fun (tname, tdef) ->
           if tname = "int"
           then println "(declare-datatypes ((int 0)) (((U42))) )"
           else (
             let env, adt =
               match tdef with
               | Mu (unique_name, adt) ->
                 let env = [ unique_name, tname ] in
                 env, adt
               | Nonrec adt -> [], adt
             in
             println
               "(declare-datatypes ((%s 0)) (( %a )) )\n%!"
               tname
               (onadt env ~tname)
               adt));
    let () =
      let args =
        match snd highlevel_typs with
        | [ (_cname, args) ] -> args
        | _ ->
          failwiths "The type of scrutinee should be a value with a single constructor"
      in
      (* Removing toplevel accessorts
         TODO: specify accessors (i.e. formal parameters' names ) in ARG0 *)
      let args = List.map snd args in
      let formal_args =
        let n = ref 0 in
        List.mapi
          (fun _i argt ->
            incr n;
            Format.sprintf "x%d" !n, argt)
          args
      in
      Format.fprintf
        ppf
        "@[<hov 2>(synth-fun func1 (%a) Int "
        (fun ppf -> List.iter (fun (name, arg) -> Format.fprintf ppf "(%s %s) " name arg))
        formal_args;
      (* the preamble *)
      (* we need to iter all the types and find all the way to access value of specific type *)
      let module M = struct
        include Map.Make (String)

        let extend k v m =
          match find k m with
          | xs -> add k (v :: xs) m
          | exception Not_found -> add k [ v ] m
        ;;
      end
      in
      let rec gather_all (acc : _ M.t) : _ -> _ = function
        | "int", _ -> acc
        | tname, tdef ->
          Format.fprintf ppf "(R%s %s) " tname tname;
          let mangle, adt =
            match tdef with
            | Nonrec adt -> Fun.id, adt
            | Mu (name, adt) ->
              ( (function
                | s when s = name -> tname
                | s -> s)
              , adt )
          in
          List.fold_left
            (fun acc (cname, cargs) ->
              let acc =
                M.extend "Bool" (Format.asprintf "((_ is %s) R%s)" cname tname) acc
              in
              let acc =
                List.fold_left
                  (fun acc (access, name) ->
                    let accessor =
                      match access with
                      | Some s -> s
                      | None -> failwith "accessor is required"
                    in
                    M.extend (mangle name) (Format.sprintf "(%s R%s)" accessor tname) acc)
                  acc
                  cargs
              in
              acc)
            acc
            adt
      in
      Format.fprintf ppf "( (Start Int) (RBool Bool) ";
      let m = List.fold_left gather_all M.empty env in
      let m =
        List.fold_left (fun acc (name, arg) -> M.extend arg name acc) m formal_args
      in
      let m =
        List.fold_left
          (fun acc (_, rhs) ->
            match rhs with
            | IR.Lit n -> M.extend "int" (string_of_int n) acc
            | _ -> acc)
          m
          Arg.clauses
      in
      Format.fprintf ppf ")@,";
      (* M.iter
         (fun k vs ->
           Format.printf "\t%s -> %a\n%!" k
             (Format.pp_print_list Format.pp_print_string)
             vs )
         m; *)
      Format.fprintf ppf "(@[<v 0>";
      Format.fprintf
        ppf
        "@[(Start Int (%a (ite RBool Start Start) ))@]@,"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
           Format.pp_print_string)
        (M.find "int" m);
      M.iter
        (fun k vs ->
          if k <> "int"
          then
            Format.fprintf
              ppf
              "(R%s %s (%a))@ "
              k
              (if k = "int" then "Int" else k)
              (Format.pp_print_list
                 ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
                 Format.pp_print_string)
              vs)
        m;
      Format.fprintf ppf "@])";
      Format.fprintf ppf " @,)@]@,"
    in
    ()
  in
  (* adding constraints. There we need to know all valid examples *)
  let () =
    for i = 1 to 10 do
      Format.fprintf ppf "(declare-var x%d Int)\n" i
    done;
    let module X = Main_inputs.ArgMake (Arg) in
    let ans : (Expr.ground * IR.logic OCanren.Std.Option.logic) list =
      Algo_fair.eval_examples (module WorkHO) (module X)
    in
    let pp_ground_list f ppf xs =
      ground_list_iteri (fun _ x -> Format.fprintf ppf " %a" f x) xs
    in
    let last_introduced = ref 0 in
    let rec pp_expr ppf = function
      | Expr.EConstr (intn, OCanren.Std.List.Nil) when Tag.string_of_tag_exn intn = "int"
        ->
        incr last_introduced;
        Format.fprintf ppf "x%d" !last_introduced
      | Expr.EConstr (name, args) ->
        let lbra, rbra = if OCanren.Std.List.Nil = args then "", "" else "(", ")" in
        Format.fprintf
          ppf
          "%s%s %a%s"
          lbra
          (Tag.string_of_tag_exn name)
          (pp_ground_list pp_expr)
          args
          rbra
    in
    Format.fprintf ppf "@,@[<v>";
    ans
    |> List.iter (fun ((expr : Expr.ground), rhs) ->
           match rhs with
           | OCanren.Value (Some (OCanren.Value (IR.Lit (OCanren.Value n)))) ->
             let (Expr.EConstr (_, args)) = expr in
             Format.fprintf
               ppf
               "@[(constraint (= %d (func1 %a)))@]@,"
               n
               (pp_ground_list pp_expr)
               args
           | _ -> ());
    Format.fprintf ppf "@]"
  in
  (* footer *)
  Format.fprintf ppf "\n(check-synth)\n%!";
  let () = close_out ch in
  let _ = Sys.command @@ Format.sprintf "cat %s" filename in
  let _ =
    Format.printf "calling cvc5....\n%!";
    Sys.command (Format.sprintf "cvc5 --lang=sygus2 --sygus-pbe %s" filename)
  in
  ()
;;
