
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

let rec list_all2 f xs0 ys0 = match xs0,ys0 with
| (x::xs, y::ys) ->
    if f x y
    then list_all2 f xs ys
    else false
| [],[] -> true
| (_::_,[]) -> false
| ([], _::_) -> false

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

(* Notation: everywhere below tag means a constructor name *)


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

(* *************************** Types thing ********************************* *)

let tinfo_names tt = match tt with T xs -> list_map fst xs
let tinfo_args tt name = match tt with
  | T xs -> list_assoc name xs
let tinfo_nth_arg tt n = match tt with T xs -> list_nth_nat n xs
let info_assoc tt name = match tt with T xs -> list_assoc name xs


let rec well_typed_expr e0 typs0 =
  match e0,typs0 with
  | (EConstr (tag, es), ts) ->
      let arg_infos = info_assoc typs0 tag in
      list_all2 well_typed_expr es arg_infos


(* *************************** IR thing ********************************* *)

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




(* *************************** Naive compilation ***************************
 * For every match clause generate as sequence of switches (that have only 2
 * branches (ifs essentially) to test where matchable starts from required
 * tag or not). It will lead to dangling `else` branches where we should
 * put code for all other clauses of pattern matching. Very ineffective
 * algorithm which generates code of exponential code size.
 *
 * Useful only for generating upper bound for compiled code size. Very stupid
 * upper bound
 *)


(* ********** evaluating matchable+scrutinee to subexpression  ************** *)
(* Receives three arguments:
 *   * expression of type epxr -- which is toplevel scrutinee,
 *   * type information for toplevel scrutinee (of type `typ_info`)
 *   * a matchable (of type `matchable`).
 * Returns subexpression of scrutinee and list of tags (a.k.a. constructor names)
 * that this subexpression can start on. This tags will be used later to
 * establish that subexpression is tested  for the tag that can be possible in
 * this possition (otherwise, this test can be optimized out).
 *
 *)
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





(* ********************* Specializable-ish IR interpreter ******************* *)
(* Essentially a negation of list_mem^o. Created from a value [x] and
 * n other values (packed to list) n disequality constraints beteen [x] and
 * list's elements.
 *
 * For eval^o purposes the code is about matchables.
 *)
let rec not_in_history x xs =
  match xs with
  | [] -> true
  | h::tl ->
      match x=h with
      | false -> not_in_history x tl
      | true -> false

(* The main function about interpretation of expressing in SWITCH langugage.
 * Arguments are the following
 *   [s] -- toplevel scrutinee
 *   [max_height] -- maximum height of patterns; is used to bound size of
 *        matchable values (looking too deep is not required because we will always
 *        met a wildcard or constructor without arguments
 *   [tinfo] -- type information for scrutinee [s]
 *   [shortcut0], [shortcut1], [shortcut_tag] -- various shortcuts
 *     that in default direction do nothing. Implementation of these shortcuts
 *     is in the beginning of module Algo_fair
 *)
let rec eval_ir s max_height tinfo shortcut0 shortcut1 shortcut_tag ir =
  (* Two mutually recursive functions that perform evaluation *)
  let rec inner history test_list irrr =
    match irrr with
    | Fail -> None
    | Lit n -> Some n
    | Switch (m, cases, on_default) ->
        match shortcut0 m max_height cases history with
        | true ->
            match eval_m s tinfo m with
            | (EConstr (etag, args), cnames) ->
                (* Если сдвиуть shortcut0 вот сюда, то будет синтезу будет плохо.
                 * В некотором смысле, то что есть -- самое оптимальное, что я нашел.
                 * Может быть, конечно, можно подобрать дургую реализацию shortcut0 для
                 * синтеза, но я не думаю, что это стоит делать до 15 мая.
                 *)
                match shortcut1 etag m cases history with
                | true ->
                    test_list (m::history) etag cnames on_default cases
    (* TODO: try to make Fail branch last *)
  in

  (* [test_list] performs evaluation of switch's branches
   * Arguments:
   *    [next_histo] -- only to perform recursive call
   *    [etag] -- tag of subscrutinee
   *    [cnames] -- tags that makes sence to test against
   *    [on_default] -- otherwise branch of switch
   *    [cases0] -- branches of switch
   *)

  let rec test_list next_histo etag cnames on_default cases0 =
    (* We iterate both over switch branches and possible tag and
     * test one after another. We expect that tags in branches is a subsequence
     * of tags in type information. So, type information cuts search branches
     * where switches are equivalent
     *)
    let rec helper constr_names cases =
      match cases=[] with
      | true -> inner next_histo test_list on_default
      | false ->
          (* Shortcut. When used in default direction does nothing
           *
           * During synthesis we make sure that branches count is
           * <= (#constr_names-1) -- switch's otherwise branch should be useful
           * We are doing so synchronously traversing cases and constr_names.
           *
           * Also we establish the order in which switch's branches are going
           * (to prune equivalent) programs.
           *
           * This may break default execution direction but for used examples it
           * works. More simple ways to implement this kind of pruning
           *   * maximum count of cases := (length constr_names - 1)
           *
           * are much slower
           *
           *)
(*           match shortcut_tag constr_names cases with
           | true ->*)
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

