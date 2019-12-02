open Mini

let ppair a b = PConstr ("pair", [a;b])
let pnil = PConstr ("nil", [])
let pwc = WildCard
let pcons a b = PConstr ("cons", [a;b])

let pp_rhs fmt = Format.fprintf fmt "%d"
let pp_maybe fa fmt = function
| None -> Format.fprintf fmt "None"
| Some x -> Format.fprintf fmt "(Some %a)" fa x

let example1 =
  [ ppair pnil pwc,  1
  ; ppair pwc  pnil, 2
  ; ppair pnil pwc,  3
  ]

let eleaf s = EConstr (s,[])
let enil = EConstr ("nil", [])
let ez = EConstr ("z", [])
let epair a b = EConstr ("pair", [a;b])

let () =
  Format.printf "%a\n%!" (pp_maybe pp_rhs) @@
  eval_pat (EConstr ("pair", [epair enil enil; enil])) example1;
  Format.printf "%a\n%!" (pp_maybe pp_rhs) @@
  eval_pat (EConstr ("pair", [epair enil enil; epair enil enil])) example1;
  ()

let () =
  (* testing IR interpreter *)
  Format.printf "%a\n%!" (pp_maybe pp_rhs) @@
  eval_ir (epair (eleaf "aaa") (eleaf "bbb")) (IFTag ("aaa", Field (Z,Scru), Int 1, Int 2));
  ()
