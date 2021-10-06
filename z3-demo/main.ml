open Z3

let __ _ =
  let ctx = mk_context [] in
  let sort123 =
    Enumeration.mk_sort
      ctx
      (Symbol.mk_string ctx "sort123")
      (List.map (Symbol.mk_int ctx) [ 1; 2; 3 ])
  in
  let neq a b = Boolean.mk_not ctx (Boolean.mk_eq ctx a b) in
  let vara = Expr.mk_fresh_const ctx "a" sort123 in
  let ph1 = neq vara (Enumeration.get_const sort123 0) in
  let ph2 = neq vara (Enumeration.get_const sort123 1) in
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [ ph1; ph2 ];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN as s -> print_endline @@ Solver.string_of_status s
  | SATISFIABLE ->
    let model = Solver.get_model solver |> Option.get in
    print_endline @@ Model.to_string model
;;

let _ =
  let ctx = mk_context [] in
  let sort123 =
    Enumeration.mk_sort
      ctx
      (Symbol.mk_string ctx "sort123")
      (List.map (Symbol.mk_int ctx) [ 1; 2; 3 ])
  in
  let neq a b = Boolean.mk_not ctx (Boolean.mk_eq ctx a b) in
  let vara = Expr.mk_fresh_const ctx "a" sort123 in
  let ph1 = neq vara (Enumeration.get_const sort123 0) in
  let ph2 = neq vara (Enumeration.get_const sort123 1) in
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [ ph1; ph2 ];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> print_endline "unsat"
  | UNKNOWN as s -> print_endline @@ Solver.string_of_status s
  | SATISFIABLE ->
    let model = Solver.get_model solver |> Option.get in
    print_endline @@ Model.to_string model
;;
