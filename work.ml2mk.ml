let list_map_all f =
  let rec helper xs = match xs with
  | [] -> true
  | y::ys -> match f y with
    | Some _ -> helper xs
    | None -> false
  in
  helper

let rec list_all f xs = match xs with
| [] -> true
| x::xs ->  if f x
            then list_all f xs
            else false

let rec same_length xs ys = match (xs, ys) with
| _::xs,_::ys -> same_length xs ys
| [],_::_ -> false
| _::_,[] -> false
| [],[] -> true

let rec list_combine xs ys =
  match xs,ys with
  | [],[] -> []
  | x::xs,y::ys -> (x, y) :: (list_combine xs ys)

type nat = Z | S of nat

let rec list_nth_nat idx xs = match (idx, xs) with
| (Z, x::_) -> x
| (S n, _::xs) -> list_nth_nat n xs

type pattern = WildCard | PConstr of string * pattern list
type expr = EConstr of string * expr list

let rec match1pat s p =
  match s,p with
  | (_,WildCard) -> true
  | (EConstr (tag1, es), PConstr (tag2, ps)) ->
      if (tag1 = tag2) && (same_length ps es)
      then
        let pairs = list_combine ps es in
        list_all (fun z -> match z with (p,e) -> match1pat e p) pairs
      else false

(* evaluation with hypothesis that all patterns are full and disjunctive *)
let rec eval_pat s pats =
  match pats with
  | [] -> None
  | (p,rhs)::ps ->
      if match1pat s p
      then Some rhs
      else eval_pat s ps

(* *************************** eval pat hacky *************************** *)
let rec eval_pat_hacky s on_fail pats =
  let rec helper acc pats = 
    match pats with
    | [] -> on_fail
    | (p,rhs)::ps ->
        (* there we check that it metaches p and doesn't match previous ones *)
        if match1pat s p
        then (match list_all (fun p -> not (match1pat s p)) acc with
              true -> rhs)
        else helper (p::acc) ps
  in 
  helper [] pats


(* *************************** IR thing ********************************* *)

type matchable = Scru | Field of nat * matchable
type ir = Fail | IFTag of string * matchable * ir * ir | Int of int

let rec eval_m s h = 
  match h with
  | Scru -> s
  | Field (n, m) ->
    match eval_m s m with
    | EConstr (_, es) -> list_nth_nat n es

let rec eval_ir s ir =
  match ir with
  | Fail -> None
  | Int n -> Some n
  | IFTag (tag, scru, th, el) ->
      match eval_m s scru with
      | EConstr (tag2, args) ->
        if tag2 = tag
        then eval_ir s th
        else eval_ir s el

let rec eval_ir_hacky s ir =
  match ir with
  | Fail -> Fail
  | Int n -> Int n
  | IFTag (tag, scru, th, el) ->
      match eval_m s scru with
      | EConstr (tag2, args) ->
        if tag2 = tag
        then eval_ir_hacky s th
        else eval_ir_hacky s el
