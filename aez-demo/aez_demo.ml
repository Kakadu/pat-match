open Aez
open Smt
module T = Term
module F = Formula
module Solver = Make (struct end)

let type_t = Hstring.make "t"
let f = Hstring.make "f"
let x = Hstring.make "x"
let y = Hstring.make "y"
let u = Hstring.make "u"
let w = Hstring.make "w"

let test1 () =
  Solver.clear ();
  Type.declare type_t [];
  Symbol.declare f [Type.type_int] type_t;
  Symbol.declare x [] Type.type_int ;
  Symbol.declare y [] Type.type_int;
  Symbol.declare u [] type_t;
  Symbol.declare w [] type_t;

  let tx = T.make_app x [] in
  let ty = T.make_app y [] in
  let tu = T.make_app u [] in
  let tw = T.make_app w [] in
  let t3 = T.make_int (Num.Int 3) in
  let t2 = T.make_int (Num.Int 2) in
  let t1 = T.make_int (Num.Int 1) in
  let fx3 = T.make_app f [T.make_arith T.Plus tx t3] in
  let fy2 = T.make_app f [T.make_arith T.Plus ty t2] in
  let ty = T.make_app y [] in

  let f1 = F.make_lit F.Eq [fx3; tu] in                          (* f(x + 3) = u *)
  let f2 = F.make_lit F.Eq [fy2; tw] in                          (* f(y + 2) = w *)
  let f3 = F.make_lit F.Eq [tx; (T.make_arith T.Minus ty t1)] in (* x = y - 1 *)
  let neg_goal = F.make F.Not [F.make_lit F.Eq [tu; tw]] in      (* not (u = w) *)

  try
    Solver.assume ~id:1 f1;
    Solver.assume ~id:2 f2;
    Solver.assume ~id:3 f3;
    Solver.assume ~id:4 neg_goal;
    Solver.check ();
    print_endline "not valid"
  with Unsat _ ->
    print_endline "valid"


let test2 () =
  Symbol.declare x [] Type.type_int;
  Symbol.declare y [] Type.type_int;
  Symbol.declare u [] Type.type_int;
  Symbol.declare w [] Type.type_int;

  let tx = T.make_app x [] in
  let ty = T.make_app y [] in
  let tu = T.make_app u [] in
  let tw = T.make_app w [] in
  let f1 = F.make_lit F.Lt [T.make_int (Num.Int 0); tx] in  (* 0 < x*)
  let f2 = F.make_lit F.Lt [tx; ty] in
  let f3 = F.make_lit F.Lt [ty; tu] in
  let f4 = F.make_lit F.Lt [tu; tw] in
  let f5 = F.make_lit F.Lt [tw; T.make_int (Num.Int 5)] in

  try
    Solver.clear();
    Solver.assume ~id:1 f1;
    Solver.assume ~id:2 f2;
    Solver.assume ~id:3 f3;
    Solver.assume ~id:4 f4;
    Solver.assume ~id:5 f5;
    Solver.check ();
    print_endline "sat"
  with Unsat _ ->
    print_endline "unsat"

let test3 () =


  let va = Hstring.make "va" in
  let vb = Hstring.make "vb" in
  let vc = Hstring.make "vc" in
  let vd = Hstring.make "vd" in
  let a = Hstring.make "a" in
  let b = Hstring.make "b" in
  let c = Hstring.make "c" in
  let d = Hstring.make "d" in
  let e = Hstring.make "e" in
  let f = Hstring.make "f" in
  let g = Hstring.make "g" in
  let h = Hstring.make "h" in
  let abc = Hstring.make "abc" in
  let efgh = Hstring.make "efgh" in

  try
    Solver.clear ();
    Type.declare abc [a; b; c];
    Type.declare efgh [e;f;g;h];
    let t = abc in
    Symbol.declare va [] t;
    Symbol.declare vb [] t;
    Symbol.declare vc [] t;
    Symbol.declare vd [] t;
    let ta = T.make_app va [] in
    let tb = T.make_app vb [] in
    let tc = T.make_app vc [] in
    let td = T.make_app vd [] in
    let f2 = F.make_lit F.Lt [ta; tb] in
    let f3 = F.make_lit F.Lt [tb; tc] in
    let f4 = F.make_lit F.Lt [tc; td] in

    Solver.assume ~id:2 f2;
    Solver.assume ~id:3 f3;
    Solver.assume ~id:4 f4;
    Solver.check ();
    print_endline "sat"
  with Unsat _ -> print_endline "unsat"
     | Error (DuplicateSymb s) -> Printf.printf "DuplicateSymb %s\n%!" (Hstring.view s)
     | Error (DuplicateTypeName s) -> Printf.printf "DuplicateTypeName %s\n%!" (Hstring.view s)
     | Error (UnknownType s) -> Printf.printf "unknown type '%s'. \n%!" (Hstring.view s)
     | Error (UnknownSymb s) -> Printf.printf "unknown symb %s %d\n%!" __FILE__ __LINE__

let () =
  (*test1 ();
  test2 ();*)
  test3 ();
  ()
