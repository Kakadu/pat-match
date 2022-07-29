type nat = Z | S of nat
type pattern = WildCard | PConstr of int * pattern list
type expr = EConstr of int * expr list

(* *)
type typ_info =
  (* list of pairs: tag of constructor and type information for every argument *)
  | T of (int * typ_info list) list

type matchable = Scru | Field of nat * matchable
type ir = Fail | ITE of matchable * int * ir * ir | Lit of int

let well_typed_expr_height height default e typs =
  let rec list_assoc name ys =
    match ys with (k, v) :: xs -> if k = name then v else list_assoc name xs
  in
  let info_assoc tt name = match tt with T xs -> list_assoc name xs in
  let rec list_all2 f xs0 ys0 =
    match (xs0, ys0) with
    | x :: xs, y :: ys -> if f x y then list_all2 f xs ys else false
    | [], [] -> true
    | _ :: _, [] -> false
    | [], _ :: _ -> false
  in
  let rec helper height e typs =
    match height with
    | Z -> e = default
    | S n -> (
        match (e, typs) with
        | EConstr (tag, es), ts ->
            let arg_infos = info_assoc typs tag in
            list_all2 (helper n) es arg_infos)
  in
  helper height e typs
(*
let compile_naively pats : ir =
  let rec list_combine xs ys =
    match (xs, ys) with
    | [], [] -> []
    | x :: xs, y :: ys -> (x, y) :: list_combine xs ys
  in
  let list_mapi f xs =
    let rec helper i xs =
      match xs with [] -> [] | x :: xs -> f i x :: helper (S i) xs
    in
    helper Z xs
  in
  let list_decorate_nat xs = list_combine (list_mapi (fun i x -> i) xs) xs in
  let rec list_foldl f acc ys =
    match ys with [] -> acc | x :: xs -> list_foldl f (f acc x) xs
  in
  let rec helper_pat scru pat rhs else_top =
    match pat with
    | WildCard -> rhs
    | PConstr (tag, args) ->
        let dec_args = list_decorate_nat args in
        let then_ =
          list_foldl
            (fun acc z ->
              match z with
              | idx, pat1 -> helper_pat (Field (idx, scru)) pat1 acc else_top)
            rhs dec_args
        in
        Switch (scru, [ (tag, then_) ], else_top)
  in
  let rec helper pats =
    match pats with
    | [] -> Fail
    | (p, rhs) :: ps ->
        let else_ = helper ps in
        helper_pat Scru p rhs else_
  in
  helper pats

type matchable_kind =
  | GoodSubTree  (** This part of scrutinee should be inspectable *)
  | MissExample
      (** In this concrete example we should not look at this part, but in matching at whole we should *)
  | MissTotally
      (** We are looking in the example too deep. We should not generate code like that *)
*)
