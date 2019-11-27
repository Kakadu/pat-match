open Base.Fn

(*
 `s` -- scrutinee
 `ps` -- list of patterns
 `candidates s ps` -- gives valuable scrutinees for patters
 `n` -- one of the RHSes of pattern matching
 `〚ps〛` -- patterns compiled to IR
 `evalPM p s n` -- interpreter for pmatch language: takes
    - [p] -- list of pairs pattern * RHS
    - [s] -- scrutinee
    - [n] -- expected RHS
  `〚ps〛` -- patterns compiled to IR


  `ps` -- always ground
  `pswitch` -- always ground
  `n` -- always ground

  fresh (s)
    candidates s ps &&& evalPM pswitch s n &&& evalIR 〚ps〛 s n
*)
type constr_name = string
let pp_constr_name fmt = Format.fprintf fmt "%S"

module Pattern = struct
  type ('name, 'xs) t  = PWildCard
                       | PConstr of 'name * 'xs

  module F = OCanren.Fmap2(struct
    type nonrec ('a, 'b) t = ('a,'b) t
    let fmap f g = function
      | PWildCard -> PWildCard
      | PConstr (name, xs) -> PConstr (f name, g xs)
  end)
  include F

  type ground = (string, ground OCanren.Std.List.ground) t
  type plogic = (string OCanren.logic, plogic OCanren.Std.List.logic) t OCanren.logic
  type injected = (ground, plogic) OCanren.injected

  let rec reifier : _ -> injected -> plogic = fun env x ->
    reify OCanren.reify (OCanren.Std.List.reify reifier) env x

  let rec prj : _ -> injected -> ground = fun env x ->
    prjc (OCanren.prjc (fun _ -> assert false))
      (OCanren.Std.List.prjc (prj) (fun _ -> assert false))
      (fun _ -> assert false)
      env x

  let rec pp_ground fmt : ground -> unit = function
    | PWildCard -> Format.fprintf fmt "_"
    | PConstr (name, Nil) -> Format.fprintf fmt "%s" name
    | PConstr (name, xs) ->
      Format.fprintf fmt "%s " name;
      GT.fmt OCanren.Std.List.ground pp_ground fmt xs;
      Format.fprintf fmt ""

  let rec pp_logic : Format.formatter -> plogic -> unit = fun fmt p ->
    GT.fmt OCanren.logic
      (fun fmt -> function
        | PWildCard -> Format.fprintf fmt "_"
        | PConstr (name, OCanren.(Value Std.List.Nil)) ->
            Format.fprintf fmt "%a" GT.(fmt OCanren.logic (fmt string)) name
        | PConstr (name, xs) ->
          Format.fprintf fmt "%a (" (GT.fmt OCanren.logic GT.(fmt string)) name;
          GT.fmt OCanren.Std.List.logic pp_logic fmt xs;
          Format.fprintf fmt ")"
      )
      fmt p

  let height (pat: ground) =
    let open OCanren.Std.List in
    let rec helper = function
    | PWildCard -> 1
    | PConstr (_, Nil) -> 1
    | PConstr (_, xs) ->
        (GT.foldl ground) (fun acc p -> max acc (helper p)) (-1000) xs
    in
    helper pat

  module ArityMap = Map.Make(Base.String)
  let get_arities (pat: ground) =
    let module M = ArityMap in
    let exception Bad in
    let rec helper acc = function
      | PWildCard -> acc
      | PConstr (name, xs) ->
          let acc =
            let arity = OCanren.Std.List.length xs in
            match M.find name acc with
            | ar when ar = arity -> acc
            | _ -> raise Bad
            | exception Not_found -> M.add name arity acc
          in
          GT.foldl OCanren.Std.List.ground (fun acc p -> helper acc p) acc xs
    in
    try Base.Result.Ok (helper M.empty pat)
    with Bad -> Base.Result.Error ()

  let check_arity pat =
    match get_arities pat with
    | Ok _ -> true
    | Error _ -> false


  let wc () : injected = OCanren.(inj @@ distrib PWildCard)
  let constr s xs : injected =
    let open OCanren  in
    inj @@ distrib (PConstr (s, xs))

  let inj p =
    let rec helper : ground -> plogic = function
    | PWildCard -> OCanren.to_logic PWildCard
    | PConstr (name, xs) ->
       OCanren.(to_logic @@ PConstr (to_logic name, OCanren.Std.List.inj helper xs))
    in
    helper p

  let pattern : ground -> injected =
    let rec foldr init f = function
    | OCanren.Std.List.Nil -> init
    | OCanren.Std.List.Cons (x, xs) -> f x (foldr init f xs)
    in

    let rec helper = function
    | PWildCard -> wc ()
    | PConstr (name, xs) ->
        constr OCanren.(inj@@lift name) @@
        foldr (OCanren.Std.List.nil ()) (fun x acc -> OCanren.Std.List.cons (helper x) acc) xs
    in
    helper
end

open Pattern
let pleaf s : ground = PConstr (s, OCanren.Std.List.of_list id [])
let ppair a b  : Pattern.ground = PConstr ("Pair", OCanren.Std.List.of_list id [a; b])
let pnil       : Pattern.ground = PConstr ("Nil",  OCanren.Std.List.of_list id [])
let pcons a b  : Pattern.ground = PConstr ("Cons", OCanren.Std.List.of_list id [a; b])
let pconstr s xs : Pattern.ground = PConstr (s, OCanren.Std.List.of_list id xs)
let pwc        = PWildCard

type match_clauses = (Pattern.ground * int) list

module Clauses = struct
  open OCanren

  type ground = (Pattern.ground * int) Std.List.ground
  type logic  = (Pattern.plogic, int OCanren.logic) OCanren.Std.Pair.logic OCanren.Std.List.logic
  type injected = (ground, logic) OCanren.injected

  let caml_to_ground ps : ground =
    List.fold_right (fun x acc -> Std.List.Cons (x,acc)) ps Std.List.Nil
  let clauses : ground -> injected = fun cs ->
    GT.foldr OCanren.Std.List.ground (fun acc (p,rhs) ->
      Std.List.cons (Std.Pair.pair (Pattern.pattern p) (inj@@lift rhs)) acc
    ) (Std.List.nil ()) cs

end

open OCanren

let make_pattern_generator pats =
  let height = List.fold_left (fun acc p -> max acc (Pattern.height p)) 0  pats in
  let arity_map =
    let default_name = ":HACK" in
    match Pattern.get_arities (PConstr (default_name, Std.List.of_list id pats)) with
    | Ok ar   -> ArityMap.remove default_name ar
    | Error _ -> failwith "bad arities"
  in
  let add_freshes n pregoal =
    let rec helper acc n =
      if n = 0 then pregoal acc
      else OCanren.Fresh.one (fun q -> helper (q::acc) (n-1))
    in
    helper [] n
  in
  let generator_0 pat = (pat === Pattern.wc ()) in
  let rec loop prev_size (prev_size_gen : Pattern.injected -> goal) =
    if prev_size > height then prev_size_gen
    else
      let next_gen =
        ArityMap.to_seq arity_map |>
        Seq.map (fun (name,c) q ->
          add_freshes c (fun vars ->
            List.fold_left (fun acc v -> acc &&& prev_size_gen v)
              (q === Pattern.constr (inj@@lift name) (Std.List.list vars))
              vars
            )
        )  |> List.of_seq |> (fun xs q -> conde @@ List.map (fun g -> g q) xs)
      in
      loop (prev_size+1) next_gen
  in
  (* generator_0 *)
  loop 0 generator_0

module Expr = struct
  type ('name, 'self) t = EConstr of 'name * 'self
    [@@deriving gt ~options:{ gmap; fmt }
    ]

  module F = OCanren.Fmap2(struct
    type nonrec ('a,'b) t = ('a, 'b) t
    let fmap eta = GT.gmap t eta
  end)
  include F

  type ground = (constr_name, ground OCanren.Std.List.ground) t
  type elogic = (constr_name logic, elogic OCanren.Std.List.logic) t logic
  type injected = (ground, elogic) OCanren.injected

  let constr s xs : injected = inj @@ distrib (EConstr (s, xs))
  let leaf s : injected = constr OCanren.(inj@@lift s) (Std.List.nil ())
  let rec reifier : _ -> injected -> elogic = fun env x ->
    reify OCanren.reify (OCanren.Std.List.reify reifier) env x

  let rec prjc : _ -> injected -> ground = fun env x ->
    F.prjc (OCanren.prjc (fun _ -> assert false))
      (OCanren.Std.List.prjc prjc (fun _ -> assert false))
      (fun _ -> assert false)
      env x

  let rec pp fmt e = GT.fmt t (GT.fmt GT.string) (GT.fmt Std.List.ground pp) fmt e
  let rec pp_logic fmt e =
    GT.fmt OCanren.logic
      (GT.fmt t (GT.fmt GT.string) (GT.fmt Std.List.logic pp_logic)) fmt e
end

let rec list_zipo cond xs ys res =
  let open Std.List in
  conde
    [ (xs === nil ()) &&& (ys === nil ()) &&& (res === Std.Bool.truo)
    ; fresh (h tl) (xs === nil ()) (ys === h%tl)   (res === Std.Bool.falso)
    ; fresh (h tl) (xs === h%tl)   (ys === nil ()) (res === Std.Bool.falso)
    ; fresh (h1 t1 h2 t2 cond_res)
        (xs === h1 % t1)
        (ys === h2 % t2)
        (cond h1 h2 cond_res)
        (conde
          [ (cond_res === Std.Bool.truo)  &&& (list_zipo cond t1 t2 res)
          ; (cond_res === Std.Bool.falso) &&& (Std.Bool.falso === res)
          ])
    ]

let rec evalPM s clauses rhs =
  let open Std.List in
  conde
    [ (clauses === nil ()) &&& failure
    ; fresh (patsH rhsH ctl line1res)
        (clauses === (Std.Pair.pair patsH rhsH)%ctl)
        (check1line s patsH line1res)
        (conde
          [ (line1res === Std.Bool.truo) &&& (rhs === rhsH)
          ; (line1res === Std.Bool.falso) &&& (evalPM s ctl rhs)
          ]
        )
    ]


and check1line scr clause res =
  fresh (name1 name2 es ps)
    (scr    === Expr.constr name1 es)
    (conde
      [ (clause === Pattern.constr name2 ps) &&&
        (conde
          [ (name1 === name2) &&& (list_zipo check1line es ps res)
          ; (name1 =/= name2) &&& (res === Std.Bool.falso)
          ])
      ; (clause === Pattern.wc ()) &&& (res === Std.Bool.truo)
      ])

module IR = struct
  type ('tag, 'fieldnum, 'rhs, 'expr, 'self) t =
    | IfTag of 'tag * 'self * 'self * 'self
    | Field of 'fieldnum * 'self
    | E of 'expr
    | Failure
    [@@deriving gt ~options:{ gmap }
    ]

  include OCanren.Fmap5(struct
    type nonrec ('tag, 'fieldnum, 'rhs, 'expr, 'self) t = ('tag, 'fieldnum, 'rhs, 'expr, 'self) t
    let fmap eta = GT.(gmap t) eta
  end)

  type ground = (constr_name,               Std.Nat.ground, Expr.ground, Expr.ground, ground) t
  type logic  = (constr_name OCanren.logic, Std.Nat.logic, Expr.elogic,  Expr.elogic, logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let iftag tag scru then_ else_ = inj @@ distrib @@ IfTag (tag, scru, then_, else_)
  let field idx x = inj @@ distrib @@ Field (idx, x)
  let e expr = inj @@ distrib @@ E expr
  let fail : IR.injected = inj @@ distrib @@ Failure
end

let () = ()

(* zero -- return 1st element, empty list -- no answer *)
let rec ntho xs idx rez =
  conde
    [ (xs === Std.List.nil ()) &&& failure
    ; fresh (tl)
        (idx === Std.Nat.zero)
        (xs === Std.List.cons rez tl)
    ; fresh (x prev h tl)
        (idx === Std.Nat.succ prev)
        (xs === Std.List.cons h tl)
        (ntho tl prev rez)
    ]

let rec evalIR : IR.injected -> Expr.injected -> _ = fun e res ->
  conde
    [ fresh (tag scru1 thenb elseb temp etag eargs)
        (e === IR.iftag tag scru1 thenb elseb)
        (evalIR scru1 temp)
        (temp === Expr.constr etag eargs)
        (conde
          [ (etag === tag) &&& (evalIR thenb res)
          ; (etag =/= tag) &&& (evalIR elseb res)
          ])
    ; fresh (idx x temp cname cargs)
        (e === IR.field idx x)
        (evalIR x temp)
        (temp === Expr.constr cname cargs)
        (ntho cargs idx res)
    ; fresh (exp)
        (e === IR.e exp)
        (exp === res)
    ]

let compile_patterns scru clauses ir =
  let open Std.List in
  conde
    [ (clauses === nil ()) &&& failure
    ; fresh (patsH rhsH ctl line1res)
        (clauses === (Std.Pair.pair patsH rhsH)%ctl)
        (check1line s patsH line1res)
        (conde
          [ (line1res === Std.Bool.truo) &&& (rhs === rhsH)
          ; (line1res === Std.Bool.falso) &&& (evalPM s ctl rhs)
          ]
        )
    ]
and compile1line s pats thenE elseE res =
  res === IR.expr (Expr.leaf "NOT_IMPLEMENTED")



let example1: (Pattern.ground * int) list =
  [ ppair pnil  pwc, 1
  ; ppair pwc  pnil, 2
  ; ppair (pcons pwc pwc) pwc, 3
  (* ; PConstr ("Nil", [pwc]), 4 *)
  ]

let () =
  assert (Pattern.check_arity @@
    PConstr ("ROOT", OCanren.Std.List.of_list id @@ List.map fst example1))

let test_evalIR () =
  let eval =
    let s : IR.injected =
      IR.field (Std.Nat.one) @@ IR.e @@
      Expr.constr (inj@@lift "Cons") (Std.List.list [Expr.leaf "Nil"; Expr.leaf "Nil2"])
    in
    evalIR s
  in
  let () = run one eval (fun r -> r#prjc Expr.prjc)
    |> OCanren.Stream.take ~n:(-1)
    |> GT.fmt GT.list Expr.pp Format.std_formatter
  in
  Format.printf "\n%!"

let test_generator () =
  let generator = make_pattern_generator @@ List.map fst example1 in
  (* let () = run one generator (fun r -> r#reify Pattern.reifier)
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list) Pattern.pp_logic Format.std_formatter
  in
  Format.printf "\n%!"; *)
  let () = run one generator (fun r -> r#prjc Pattern.prj)
    |> OCanren.Stream.take ~n:(15)
    |> GT.(fmt list) Pattern.pp_ground Format.std_formatter
  in
  Format.printf "\n%!";
  ()

let testEvalPM1 () =
  let evalPM rhs =
    let s =
      (* ("a"::"a", "a" :: "a") *)
      let down = Expr.constr OCanren.(inj@@lift "a") (OCanren.Std.List.nil ()) in
      let cns =
        Expr.(constr OCanren.(inj@@lift "Cons")
        (OCanren.Std.List.list [down; down]))
      in
      (* let cns = Expr.(constr OCanren.(inj@@lift "Nil") (Std.List.nil ())) in *)
      Expr.(constr (inj@@lift "Pair") (OCanren.Std.List.list [cns; cns]))
    in
    evalPM s Clauses.(clauses @@ caml_to_ground example1) rhs
  in
  let () = run one evalPM (fun r -> r#prjc (OCanren.prjc (fun _ -> assert false)))
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list (fmt int)) Format.std_formatter
  in
  Format.printf "\n%!"

let testEvalPM2 () =
  let evalPM rhs =
    let s =
      Expr.constr OCanren.(inj@@lift "Nil") @@
      Std.List.list [ Expr.leaf "A" ]
    in
    let clauses : (Pattern.ground * int) list =
      [ pconstr "Ni" [], 1
      ; pconstr "Nil" [ pconstr "A" []], 2
      ]
    in
    let c1  = Clauses.caml_to_ground clauses in
    evalPM s Clauses.(clauses c1) rhs
  in
  let () = run one evalPM (fun r -> r#prjc (OCanren.prjc (fun _ -> assert false)))
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list (fmt int)) Format.std_formatter
  in
  Format.printf "\n%!"

let testEvalPM3 () =
  let evalPM rhs =
    let s =
      (* ("a"::"a", "a" :: "a") *)
      let down = Expr.constr OCanren.(inj@@lift "a") (OCanren.Std.List.nil ()) in
      let cns =
        Expr.(constr OCanren.(inj@@lift "Cons")
        (OCanren.Std.List.list [down; down]))
      in
      let cns = Expr.(leaf "Nil") in
      Expr.(constr (inj@@lift "Pair") (OCanren.Std.List.list [cns; cns]))
    in
    let example: (Pattern.ground * int) list =
      [ pwc , 3
      ; ppair pnil  pwc, 1
      ; ppair pwc  pnil, 2
      ;
      (* ; ppair (pcons pwc pwc) pwc, 3 *)
      (* ; PConstr ("Nil", [pwc]), 4 *)
      ]
    in
    evalPM s Clauses.(clauses @@ caml_to_ground example) rhs
  in
  let () = run one evalPM (fun r -> r#prjc (OCanren.prjc (fun _ -> assert false)))
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list (fmt int)) Format.std_formatter
  in
  Format.printf "\n%!"

let testAll () =
  ()
  (* let evalPM progIR =
    let example1: (Pattern.ground * _) list =
      [ ppair pnil  pwc, Expr.leaf "X"
      ; ppair pwc  pnil, Expr.leaf "Y"
      ; ppair (pcons pwc pwc) pwc, Expr.leaf "Z"
      ]
    in
    fresh (scru)
      (make_pattern_generator (List.map fst example1) scru)
      (evalPM scru Clauses.(clauses @@ caml_to_ground example1) progIR)
      (evalIR)
  in
  let () = run one evalPM (fun r -> r#prjc (OCanren.prjc (fun _ -> assert false)))
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list (fmt int)) Format.std_formatter
  in
  Format.printf "\n%!" *)

let main =
  (* testEvalPM2 ();
  testEvalPM3 (); *)
  testEvalPM1 ();
  test_evalIR ()
  testAll ();


(*
match scru with
| ([], _) -> 1
| (_, []) -> 2
| (_::_, _) -> 3
*)
