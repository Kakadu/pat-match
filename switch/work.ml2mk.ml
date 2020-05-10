type nat = Z | S of nat

let nat_lt a b =
  let rec helper root =
    match root with
    | (_, Z) -> false
    | (Z, S _) -> true
    | (S x, S y) -> helper (x,y)
  in
  helper (a,b)

let nat_leq a b =
  let rec helper root =
    match root with
    | (Z,_) -> true
    | (S _, Z) -> false
    | (S x, S y) -> helper (x,y)
  in
  helper (a,b)

let fst z = match z with (a,_) -> a

let rec list_mem x xs =
  match xs with
  | [] -> false
  | h::tl -> if x=h then true else list_mem x tl

let rec list_assoc name ys =
  match ys with
  | (k,v)::xs ->
      if k = name
      then v
      else list_assoc name xs

let list_map_all f =
  let rec helper xs = match xs with
  | [] -> true
  | y::ys -> match f y with
    | Some _ -> helper xs
    | None -> false
  in
  helper

let list_map f xs =
  let rec helper xs = match xs with
  | [] -> []
  | x::xs -> (f x) :: helper xs
  in
  helper xs

let list_mapi f xs =
  let rec helper i xs = match xs with
  | [] -> []
  | x::xs -> (f i x) :: helper (S i) xs
  in
  helper Z xs

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

let rec list_foldl f acc ys = match ys with
| [] -> acc
| x::xs -> list_foldl f (f acc x) xs

let list_decorate_nat xs =
  list_combine (list_mapi (fun i x -> i) xs) xs

let rec list_nth_nat idx xs = match (idx, xs) with
| (Z, x::_) -> x
| (S n, _::xs) -> list_nth_nat n xs

(* ************************************************************************** *)
(* we can't make proper alias because noCanren doesn't support it *)
(* type tag = int *)
type pattern =
  | WildCard
  | PConstr of nat * pattern list
type expr = EConstr of nat * expr list

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
type ir =
  | Fail
  | Switch of matchable * (nat * ir) list * ir
(*  | IFTag of tag * matchable * ir * ir*)
  | Lit of int
type typ_info = T of (nat * typ_info list) list

let rec height_of_matchable root =
  match root with
  | Scru -> S Z
  | Field (_, ss) -> S (height_of_matchable ss)

let matchable_leq_nat m n =
  let rec helper root =
    match root with
    | (Scru, Z) -> false
    | (Scru, S _) -> true
    | (Field (_,m1), S n1) -> helper (m1,n1)
    | (Field (_,_), Z) -> false
  in
  helper (m,n)

(* *************************** Naive compilation *************************** *)
let compile_naively pats: ir =
  let rec helper_pat scru pat rhs else_top =
    match pat with
    | EConstr (tag, args) ->
        let dec_args = list_decorate_nat args in
        let else_ =
          list_foldl (fun acc z -> match z with (idx, pat1) ->
              helper_pat (Field (idx, scru)) pat1 acc else_top
          ) rhs dec_args
        in
        Switch (scru, [ (tag, rhs) ], else_)
  in
  let rec helper pats =
    match pats with
    | [] -> Fail
    | (p,rhs)::ps ->
        let else_ = helper ps in
        helper_pat Scru p rhs else_
  in
  helper pats

let tinfo_names tt = match tt with T xs -> list_map fst xs
let tinfo_args tt name = match tt with
  | T xs -> list_assoc name xs
let tinfo_nth_arg tt n = match tt with T xs -> list_nth_nat n xs
let info_assoc tt name = match tt with T xs -> list_assoc name xs

(* ****************************** evaluating IR ************************** *)
let rec eval_m s typinfo0 path0 =
  let rec helper path =
    match path with
    | Scru -> (s, typinfo0)
    | Field (nth, scru) ->
      match helper scru with
      | (EConstr (cname, es), next_tinfos) ->
          let arg_info = info_assoc next_tinfos cname in
          (list_nth_nat nth es, list_nth_nat nth arg_info)
  in
  match helper path0 with
  | (ans, info) ->  (ans, tinfo_names info)
(*
let is_ordered prev next =
  match prev with
  | None -> true
  | Some p -> nat_lt p next*)

(*let bound_cases cases upper =
  let rec helper arg =
    match arg with
    | (_,[]) -> false
    | ([], _::_) -> true
    | (_::ys, _::zs) -> helper (ys, zs)
    in
  (* cases *)
  match cases = [] with
  | false -> helper (cases, upper)
*)

(*
let rec eval_ir_hacky s tinfo ir =
  match ir with
  | Fail -> Fail
  | Int n -> Int n
  | IFTag (tag, scru, th, el) ->
      match fst (eval_m s tinfo scru ) with
      | EConstr (tag2, args) ->
        if tag2 = tag
        then eval_ir_hacky s tinfo th
        else eval_ir_hacky s tinfo el
*)

(* *************************** Naive compilation *************************** *)
let compile_naively pats : ir =
  let rec helper_pat scru pat rhs else_top =
    match pat with
    | WildCard -> rhs
    | PConstr (tag, args) ->
        let dec_args = list_decorate_nat args in
        let then_ =
          list_foldl (fun acc z -> match z with (idx, pat1) ->
              helper_pat (Field (idx, scru)) pat1 acc else_top
          ) rhs dec_args
        in
        Switch (scru, [(tag,then_)], else_top)
  in
  let rec helper pats =
    match pats with
    | [] -> Fail
    | (p,rhs)::ps ->
        let else_ = helper ps in
        helper_pat Scru p rhs else_
  in
  helper pats


(* ********************* Specializable-ish IR interpreter ******************* *)
let rec not_in_history x xs =
  match xs with
  | [] -> true
  | h::tl ->
      match x=h with
      | false -> not_in_history x tl
      | true -> false

let rec eval_ir s max_height tinfo shortcut1 shortcut_tag ir =
  let rec inner history test_list irrr =
    match irrr with
    | Fail -> None
    | Lit n -> Some n
    | Switch (m, cases, on_default) ->
        match matchable_leq_nat m max_height with
        | true ->
        match cases = [] with
        | false ->
            match eval_m s tinfo m with
            | (EConstr (etag, args), cnames) ->
                match shortcut1 etag m cases history with
                | true ->
                (*match not_in_history m history with
                | true ->*)
                    test_list (m::history) etag cnames on_default cases
    (* TODO: try to make Fail branch last *)
  in

  let rec test_list next_histo etag cnames on_default cases0 =
    let rec helper constr_names cases =
      match cases=[] with
      | true -> inner next_histo test_list on_default
      | false ->
          match shortcut_tag constr_names cases with
          | true ->
          match constr_names with
          | constr_hd :: constr_tl ->
            match cases with
            | (qtag, ontag) :: clauses_tl ->
                  match qtag = constr_hd with
                  | true  -> begin
                      match qtag = etag with
                      | true ->  inner next_histo test_list ontag
                      | false -> helper constr_tl clauses_tl
                  end
                  | false -> helper constr_tl cases
    in
    helper cnames cases0
  in

  inner [] test_list ir
