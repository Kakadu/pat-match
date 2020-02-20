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

let rec list_foldl f acc ys = match ys with
| [] -> acc
| x::xs -> list_foldl f (f acc x) xs

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

let list_mapi f xs =
  let rec helper i xs = match xs with
  | [] -> []
  | x::xs -> (f i x) :: helper (S i) xs
  in
  helper Z xs

let list_map f xs =
  let rec helper xs = match xs with
  | [] -> []
  | x::xs -> ( x) :: helper xs
  in
  helper xs

let rec list_append xs ys =
  match xs with
  | [] -> ys
  | x::xs -> x :: (list_append xs ys)

let list_snoc x xs = list_append xs [x]

let rec list_nth_nat idx xs = match (idx, xs) with
| (Z, x::_) -> x
| (S n, _::xs) -> list_nth_nat n xs

let option_bind x f =
  match x with
  | None -> None
  | Some y -> f y

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

let rec match_pat_bindings s p =
  match s,p with
  | (_,WildCard) -> Some []
  | (EConstr (tag1, es), PConstr (tag2, ps)) ->
    if (tag1 = tag2) && (same_length ps es)
    then
      let pairs = list_combine ps es in
      let triples = list_mapi (fun i x -> (i,x)) pairs in
      list_foldl (fun acc pe -> match pe with (n,next) -> match next with (pat,e) ->
          option_bind acc (fun old ->
          option_bind (match_pat_bindings e pat) (fun new_ ->
          Some (list_append new_ old) )))
        (Some []) triples
      (*list_all (fun z -> match z with (p,e) -> match1pat e p) pairs*)
    else None



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

let do_not_match s eval_guard prev =
  let rec helper ys =
    match ys with
    | [] -> true
    | (p,g)::xs ->
      match match_pat_bindings s p with
      | None -> true
      | Some bnds ->
          match g with
          | None -> false
          | Some guard ->
              if eval_guard bnds guard
              then false
              else helper xs
  in
  helper prev

let rec eval_with_guards s on_fail eval_guard pats =
  let rec helper acc pats =
    match pats with
    | [] -> on_fail
    | (p, aux)::ps ->
        match aux with (g, rhs) ->
        (* there we check that  it metaches p and doesn't match previous ones *)
        match match_pat_bindings s p with
        | None -> helper (list_snoc (p,g) acc) ps
        | Some bindings ->
            match g with
            | None -> rhs
            | Some guard ->
                if eval_guard bindings guard
                then (match do_not_match s eval_guard acc with true -> rhs)
                else helper (list_snoc (p,g) acc) ps

  in
  helper [] pats



(* *************************** IR thing ********************************* *)

type matchable = Scru | Field of nat * matchable
type ir =
  | Fail | Int of int
  | IFTag of string * matchable * ir * ir
  | IFGuard of nat * ir list * ir * ir

let rec eval_m s h eval_guard =
  match h with
  | Scru -> s
  | Field (n, m) ->
    match eval_m s m eval_guard with
    | EConstr (_, es) -> list_nth_nat n es

let rec eval_ir s eval_guard ir =
  match ir with
  | Fail -> None
  | Int n -> Some n
  | IFTag (tag, scru, th, el) ->
      match eval_m s scru eval_guard with
      | EConstr (tag2, args) ->
        if tag2 = tag
        then eval_ir s eval_guard th
        else eval_ir s eval_guard el


let rec eval_ir_hacky s eval_guard ir =
  match ir with
  | Fail -> Fail
  | Int n -> Int n
  | IFGuard (gndx, args, then_, else_) ->
      let evaled_args = list_map (fun x -> eval_ir_hacky s eval_guard x) args in
      if eval_guard gndx evaled_args
      then eval_ir_hacky s eval_guard then_
      else eval_ir_hacky s eval_guard else_
  | IFTag (tag, scru, th, el) ->
      match eval_m s scru eval_guard with
      | EConstr (tag2, args) ->
        if tag2 = tag
        then eval_ir_hacky s eval_guard th
        else eval_ir_hacky s eval_guard el

let app f x = f x
