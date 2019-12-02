let list_map_all f xs =
  let rec helper = function
  | [] -> true
  | x::xs -> match f x with
  | Some _ -> helper xs
  | None -> false
  in
  helper xs

let rec list_all f = function
| [] -> true
| x::xs ->  if f x
            then list_all f xs
            else false

let rec list_length = function
| [] -> 0
| x::xs -> 1 + list_length xs

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

let rec eval_pat s pats =
  match pats with
  | [] -> None
  | (p,rhs)::ps ->
      if eval1pat s p
      then Some rhs
      else eval_pat s ps

and eval1pat s p =
  match s,p with
  | (_,WildCard) -> true
  | (EConstr (tag1, es), PConstr (tag2, ps)) ->
      if (tag1 = tag2) && (list_length ps = list_length es)
      then
        let pairs = list_combine ps es in
        list_all (fun (p,e) -> eval1pat e p) pairs
      else false

(* *************************** IR thing ********************************* *)

type matchable = Scru | Field of nat * matchable
type ir = Fail | IFTag of string * matchable * ir * ir | Int of int


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
and eval_m s = function
  | Scru -> s
  | Field (n, m) ->
    match eval_m s m with
    | EConstr (_, es) -> list_nth_nat n es
