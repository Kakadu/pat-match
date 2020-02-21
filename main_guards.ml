module Work = Work_guards
open Work
open OCanren
open Tester

let id x = x

let pp_rhs fmt = Format.fprintf fmt "%d"
let pp_maybe fa fmt = function
| None -> Format.fprintf fmt "None"
| Some x -> Format.fprintf fmt "(Some %a)" fa x

let leaf s = eConstr !!s @@ Std.List.nil ()
let pair a b = eConstr !!"pair" (Std.List.list [a;b])

type name = string
let name =
  { GT.gcata = ()
  ; fix = ()
  ; plugins = object
      method fmt f = Format.fprintf f "%s"
  end }

(* TODO: put this to stdlib *)
let rec inject_ground_list ps =
  (* TODO: tail recursion *)
  let rec helper = function
  | Std.List.Nil -> Std.List.nil ()
  | Std.List.Cons (x, xs) -> Std.List.cons x (helper xs)
  in
  helper ps

module Pattern = struct
  type ('s,'ps) t = ('s,'ps) Work.gpattern = WildCard | PVar of 's | PConstr of 's * 'ps
    [@@deriving gt ~options:{fmt; gmap}]

  type ground = (string, ground Std.List.ground) t
  type logic = (string OCanren.logic, logic Std.List.logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = pConstr
  let wc = wildCard
  let var = pVar

  let rec height = function
  | WildCard  -> 0
  | PVar _ -> 1
  | PConstr (_,ps) ->
    GT.foldl Std.List.ground (fun acc x -> max acc (height x)) 0 ps + 1

  let ground_list_length xs =
    GT.foldl Std.List.ground (fun acc _ -> acc+1) 0 xs

  let show p =
    let rec helper = function
    | WildCard -> "_"
    | PVar s -> s
    | PConstr (s, Std.List.Nil) -> Printf.sprintf "(%s)" s
    | PConstr (s, ps) ->
      Printf.sprintf "(%s %s)" s (GT.show Std.List.ground helper ps)
    in
    helper p

  let rec show_logic (p: logic) =
    let rec helper = function
    | WildCard -> "_"
    | PVar s -> GT.show OCanren.logic (GT.show GT.string) s
    | PConstr (s, OCanren.Value Std.List.Nil) ->
        GT.show OCanren.logic (GT.show GT.string) s
    | PConstr (s, ps) ->
      Printf.sprintf "(%s %s)"
        (match s with
          | OCanren.Value s -> s
          | s -> GT.show OCanren.logic (GT.show GT.string) s)
        (GT.show Std.List.logic show_logic ps)
    in
    GT.show OCanren.logic helper p

  let rec inject : ground -> injected = fun p ->
    match p with
    | WildCard -> wc ()
    | PVar s -> var !!s
    | PConstr (name,ps) ->
        constr !!name @@
        (inject_ground_list @@ GT.gmap Std.List.ground inject ps)

  module ArityMap = Map.Make(Base.String)
  exception Bad

  let get_arities (pat: ground) =
    let rec helper acc = function
      | WildCard
      | PVar _    -> acc
      | PConstr (name, xs) ->
          let acc =
            let arity = ground_list_length xs in
            try
              match ArityMap.find name acc with
              | ar when ar = arity -> acc
              | _ -> raise Bad
            with  Not_found -> ArityMap.add name arity acc
          in
          GT.foldl OCanren.Std.List.ground (fun acc p -> helper acc p) acc xs
    in
    try Some (helper ArityMap.empty pat)
    with Bad -> None
end

module Expr = struct
  type ground = (string, ground Std.List.ground) gexpr
  type logic  = (string OCanren.logic, logic Std.List.logic) gexpr OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = eConstr
  let econstr s xs = EConstr (s, Std.List.of_list id xs)

  let show x =
    let rec helper pars x =
     match x with
    | EConstr (s, Std.List.Nil) when pars -> Printf.sprintf "(%s)" s
    | EConstr (s, Std.List.Nil)           -> s
    | EConstr (s, xs) when pars ->
      Printf.sprintf "(%s %s)"
        (GT.show GT.string s)
        (GT.show Std.List.ground (helper false) xs)
    | EConstr (s, xs) ->
      Printf.sprintf "%s %s"
        (GT.show GT.string s)
        (GT.show Std.List.ground (helper false) xs)
    in
    helper false x

  let rec show_logic x =
    let rec helper x =
      match x with
      | EConstr (s, xs) ->
        Printf.sprintf "(%s %s)"
          (GT.show OCanren.logic (GT.show GT.string) s)
          (GT.show Std.List.logic show_logic xs)
    in
    GT.show OCanren.logic helper x

  let rec reify env x =
    For_gexpr.reify OCanren.reify (Std.List.reify reify) env x

  let inject (e: ground) : injected =
    let rec helper = function
    | EConstr (s,xs) ->
        constr !!s (inject_ground_list @@ GT.gmap Std.List.ground helper xs)
    in
    helper e
end

let print_demos msg xs =
  Printf.printf "<%s>\n" msg;
  List.iter (fun p -> Printf.printf "\t\t%s\n" (Expr.show p)) xs;
  Printf.printf "</%s>\n" msg


let generate_demo_exprs pats =
  let height = List.fold_left
    (fun acc p -> max acc (Pattern.height p)) 0 pats in
  Printf.printf "height = %d\n%!" height;

  let arity_map =
    let default_name = ":HACK" in
    match Pattern.get_arities (PConstr (default_name, Std.List.of_list id pats)) with
    | Some ar -> Pattern.ArityMap.remove default_name ar
    | None    -> failwith "bad arities"
  in

  let dummy = Expr.econstr "DUMMY" [] in
  let height1 =
    Pattern.ArityMap.fold (fun k arity acc ->
      (Expr.econstr k @@ List.init arity (fun _ -> dummy)) :: acc
    ) arity_map []
  in
  let () = print_demos "height1" height1 in

  let rec populate_lists : int -> 'a list -> 'a list list = fun n init ->
    if n<1 then assert false
    else if n = 1 then List.map (fun h -> [h]) init
    else
      List.flatten @@ List.map (fun xs -> List.map (fun h -> h::xs) init) @@
      populate_lists (n-1) init
  in

  let rec builder (prev: 'a list) curh : Expr.ground list =
    if curh > height
    then prev
    else
      Pattern.ArityMap.to_seq arity_map
      |> Seq.flat_map (fun (name,arity) ->
          if arity = 0 then Seq.return @@ Expr.econstr name []
          else
            List.to_seq @@
            List.map (Expr.econstr name) @@
            populate_lists arity prev
      )
      |> List.of_seq
  in
  builder height1 (1+1)

(*let checkAnswer q ir eval_guard r = eval_ir ((===) q) ((===) ir) eval_guard r

let _ =
  run_exn (Format.asprintf "%a" (pp_maybe pp_rhs)) 1 q qh ("answers", fun q ->
    checkAnswer (pair (leaf "aaa") (leaf "bbb"))
      (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
      (fun _  -> failure)
      q
  )

let _ =
  runR Expr.reify Expr.show Expr.show_logic
        1 q qh ("answers", fun q ->
     checkAnswer
        q
        (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
        (fun _  -> failure)
        (Std.some (!!2))
  )*)

let add_freshes n pregoal =
  let rec helper acc n =
    if n = 0 then pregoal acc
    else OCanren.Fresh.one (fun q -> helper (q::acc) (n-1))
  in
  helper [] n

let pwc = WildCard
let pconstr name xs = PConstr (name, Std.List.of_list id xs)
let pvar name = PVar name
let pleaf s = pconstr s []
let pnil    = pleaf "nil"
let pcons a b = pconstr "cons" [a;b]
let psome a   = pconstr "some" [a]
let ppair a b : Pattern.ground = pconstr "pair" [a;b]

module Nat = struct
  type 'a gnat = 'a Work.gnat = Z | S of 'a [@@deriving gt ~options:{fmt}]
  type ground = ground gnat
  type logic = logic gnat OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let z : injected = Work.z ()
  let s = Work.s

  let show (n: ground) =
    let rec helper acc = function
    | Z -> string_of_int acc
    | S n -> helper (acc+1) n
    in
    helper 0 n

  let show_logic n =
    let rec helper acc : logic -> string = function
    | Value Z -> string_of_int acc
    | Value (S n) -> helper (acc+1) n
    | (Var _) as n ->
        if acc <= 0
        then GT.show OCanren.logic (show_gnat_logic 0) n
        else Printf.sprintf "(%d+%s)" acc (GT.show OCanren.logic (show_gnat_logic 0) n)
    and show_gnat_logic acc : logic gnat -> string = function
    | Z -> string_of_int acc
    | S n -> helper (acc+1) n
    in
    helper 0 n

  let pp_logic fmt x = Format.fprintf fmt "%s" (show_logic x)

  let rec inject = function
  | Z -> z
  | S x -> s (inject x)

  let fmt formatter x = Format.fprintf formatter "%s" (show x)
  let rec reify env x = For_gnat.reify reify env x
end

module Matchable = struct
  type ground = (Nat.ground, ground) gmatchable
  type logic = (Nat.logic, logic) gmatchable OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let scru = scru
  let field = field
  let rec reify env x =
    For_gmatchable.reify Nat.reify reify env x

  let rec show_logic x =
    let rec helper = function
    | Scru          -> "Scru"
    | Field (n,r) ->
      Printf.sprintf "(field %s %s)" (Nat.show_logic n) (show_logic r)
    in
    GT.show OCanren.logic helper x

  let pp_logic fmt (x: logic) = Format.fprintf fmt "%s" (show_logic x)

  let show x =
    let rec helper = function
    | Scru        -> "Scru"
    | Field (n,r) -> Printf.sprintf "(field %s %s)" (Nat.show n) (helper r)
    in
    helper x

  let pp fmt (x: ground) = Format.fprintf fmt "%s" (show x)
  let fmt formatter x = Format.fprintf formatter "%s" (show x)
end


module IR = struct
  type ground = (int, string, Matchable.ground
                , Nat.ground, (string * Matchable.ground) Std.List.ground, ground
                ) gir
  type logic =
    ( int OCanren.logic, string OCanren.logic, Matchable.logic
    , Nat.logic, (string OCanren.logic, Matchable.logic) Std.Pair.logic Std.List.logic, logic
    ) gir OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let fail = fail
  let iftag = iFTag
  let int = int

  let eint n = Int n

  let rec reify env (x: injected) : logic =
    For_gir.reify OCanren.reify OCanren.reify Matchable.reify Nat.reify
      (Std.List.reify @@ Std.Pair.reify OCanren.reify Matchable.reify) reify
      env x

  let inject e =
    let rec helper = function
    | Int n -> int !!n
    | _ -> failwith "not implemented"
    in
    helper e

  let rec pp fmt : ground -> unit = function
  | Fail -> Format.fprintf fmt "(fail)"
  | Int n -> Format.fprintf fmt "%d" n
  | IFTag (str, m, th_, el_) ->
    Format.fprintf fmt "(iftag %S %a %a %a)"
      str
      Matchable.fmt m
      pp th_
      pp el_
  | IFGuard (ndx, args, th_, el_) ->
      Format.fprintf fmt "(ifguard %a %a %a %a)"
        Nat.fmt ndx
        (GT.fmt Std.List.ground @@ GT.fmt Std.Pair.ground (GT.fmt GT.string) Matchable.pp) args
        pp th_
        pp el_

  let show e = Format.asprintf "%a" pp e

  let rec pp_logic fmt : logic -> unit =
    let rec helper fmt = function
    | Fail -> Format.fprintf fmt "(fail)"
    | Int ln -> Format.fprintf fmt "%a" (GT.fmt OCanren.logic (GT.fmt GT.int)) ln
    | IFTag (ltag, m, th_, el_) ->
        Format.fprintf fmt "(iftag %a %a %a %a)"
          (GT.fmt OCanren.logic (GT.fmt GT.string)) ltag
          Matchable.pp_logic m
          (GT.fmt OCanren.logic helper) th_
          (GT.fmt OCanren.logic helper) el_
    | IFGuard (ndx, args, th_, el_) ->
        Format.fprintf fmt "(ifguard %a %a %a %a)"
          Nat.pp_logic ndx
          (GT.fmt Std.List.logic @@ GT.fmt Std.Pair.logic (GT.fmt OCanren.logic @@ GT.fmt GT.string) Matchable.pp_logic) args
          (GT.fmt OCanren.logic helper) th_
          (GT.fmt OCanren.logic helper) el_
    in
    GT.fmt OCanren.logic helper fmt

  let show_logic e = Format.asprintf "%a" pp_logic e
end

module Triple = struct
  type ('a,'b,'c) t = 'a * 'b * 'c [@@deriving gt ~options:{fmt; gmap }]
  module F = Fmap3(struct
    type nonrec ('a,'b,'c) t = ('a,'b,'c) t
    let fmap eta = GT.gmap t eta
  end)

  type ('a,'b,'c) ground = ('a,'b,'c) t
  type ('a,'b,'c) logic = ('a,'b,'c) t OCanren.logic
  type ('a,'b,'c,'d,'e,'f) injected = (('a,'b,'c) ground, ('d,'e,'f) logic) OCanren.injected

  let make a b c = inj @@ F.distrib (a,b,c)
  let reify = F.reify
end

module Clauses = struct
  type ground = (Pattern.ground * IR.ground) Std.List.ground
  type logic = (Pattern.logic, IR.logic) Std.Pair.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected
end

module Clauses_with_guards = struct
(*  type ground = (Pattern.ground, Nat.ground, IR.ground) Triple.ground Std.List.ground
  type logic  = (Pattern.logic,  Nat.logic,  IR.logic)  Triple.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected*)

  type ground = (Pattern.ground * (Nat.ground option * IR.ground)) Std.List.ground
  type logic  = (Pattern.logic, (Nat.logic Std.Option.logic, IR.logic) Std.Pair.logic) Std.Pair.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected
end


let inject_patterns ps =
  let option_inject fa = function
  | None -> Std.Option.none ()
  | Some x ->Std.Option.some (fa x)
  in

  Std.List.list @@
  List.map (fun (p,(g,rhs)) ->
    Std.Pair.pair (Pattern.inject p) @@
    Std.Pair.pair (option_inject Nat.inject g) (IR.inject rhs)
  ) ps

let eval_pat :
  Expr.injected ->
  Clauses.injected ->
  (IR.ground option, IR.logic Std.Option.logic) OCanren.injected ->
  goal
  = fun expr_scru pats res -> eval_pat ((===)expr_scru) ((===)pats) res

let eval_ir :
  Expr.injected ->
  ( Nat.injected ->
    Expr.injected ->
    (string * Matchable.ground, (string OCanren.logic, Matchable.logic) Std.Pair.logic) Std.List.groundi ->
    (bool, bool OCanren.logic) OCanren.injected -> goal) ->
  onfail:IR.injected ->
  IR.injected ->
  IR.injected -> goal
  = fun s eval_guard ~onfail ir res ->
      eval_ir_hacky
        ((===)s)
        (fun n s xs rez -> Fresh.three (fun x y z -> (n x) &&& (s y) &&& (xs z) &&& (eval_guard x y z rez)))
        ((===)onfail)
        ((===)ir)
        res

(*
let main ?(n=10) patterns2 =
(*
  let patterns2 : (Pattern.ground * IR.ground) list =
    (* [ psome pnil, IR.eint 1
    ; psome  pwc, IR.eint 2
    ] *)
    (* [  pwc, IR.eint 1
    ; pnil, IR.eint 2
    ] *)
    (* [ ppair pnil pwc, IR.eint 1
    ; ppair pwc  pnil, IR.eint 2
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 3
    ] *)
    [ ppair pnil pwc,  IR.eint 1
    ; ppair pwc  pnil, IR.eint 2
    ; ppair pnil pnil, IR.eint 3
    (* ; pwc, IR.eint 4 *)
    ]
  in*)
  let injected_pats = inject_patterns patterns2 in

  let injected_exprs =
    let demo_exprs = generate_demo_exprs @@ List.map (fun (x,_,_) -> x) patterns2 in
    Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;
    print_demos "demo_exprs" demo_exprs;
    let demo_exprs =
      demo_exprs |> List.filter (fun e ->
        let open OCanren in
        run one
          (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
          (fun r -> r)
          |> (fun s -> not (OCanren.Stream.is_empty s))
        )
    in
    demo_exprs |> List.iter (fun e ->
        runR (Std.Option.reify IR.reify)
             (GT.show Std.Option.ground IR.show)
             (GT.show Std.Option.logic IR.show_logic)
          1 q qh (Printf.sprintf "test_demo: `%s`" (Expr.show e), fun ir ->
            eval_pat (Expr.inject e) injected_pats (ir)
        )
      );
    print_newline ();
    List.map Expr.inject demo_exprs
  in

  runR IR.reify IR.show IR.show_logic n
    q qh ("ideal_IR", fun ideal_IR ->
      let init =
        fresh (hack1 hack2)
          success
          (* (ideal_IR === IR.iftag !!"pair" (Matchable.scru ()) hack1 hack2) *)
      in

      List.fold_left (fun acc (scru: Expr.injected) ->
        fresh (res_pat res_ir)
          acc
          (eval_pat scru injected_pats res_pat)
          (eval_ir  scru (fun _ -> failure) ideal_IR      res_ir)
          (conde
            [ fresh (n)
                (res_pat === Std.Option.some (IR.int n))
                (res_ir  === Std.Option.some n)
            ; (res_pat === Std.Option.none ()) &&& (res_ir === Std.Option.none())
            ])
      ) init injected_exprs
    );

  ()
*)

let eval_pat_hacky :
  Expr.injected ->
  IR.injected ->
  Clauses.injected ->
  IR.injected ->
  goal
  = fun expr_scru onfail pats res -> eval_pat_hacky ((===)expr_scru) ((===)onfail) ((===)pats) res

let wrap :
  ( (_,_) OCanren.injected -> (_,_) OCanren.injected -> (_,_) OCanren.injected -> goal) ->
  ((_,_) OCanren.injected -> goal) -> ((_,_) OCanren.injected -> goal) -> (_,_) OCanren.injected -> goal
  = fun eval_guard ->
   fun a b z -> Fresh.two (fun x y -> (a x) &&& (b y) &&& (eval_guard x y z))

(*let eval_ir_hacky :
  Expr.injected ->
  ( (_,_) OCanren.injected -> (_,_) OCanren.injected -> (_,_) OCanren.injected -> goal) ->
  IR.injected ->
  IR.injected ->
  goal
  = fun s eval_guard ir res ->
      eval_ir_hacky ((===)s)
        (fun a b z -> Fresh.two (fun x y -> (a x) &&& (b y) &&& (eval_guard x y z)))
        ((===)ir) res*)

(*
let run_hacky ?(n=10) patterns2 =
  let injected_pats = inject_patterns patterns2 in

  let injected_exprs,non_exh_pats =
    let demo_exprs = generate_demo_exprs @@ List.map fst patterns2 in
    Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;
    print_demos "demo_exprs" demo_exprs;
    let (demo_exprs,non_exh_pats) =
      demo_exprs |> List.partition (fun e ->
        let open OCanren in
        run one (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
          (fun r -> r)
          |> (fun s -> not (OCanren.Stream.is_empty s))
        )
    in
    demo_exprs |> List.iter (fun e ->
        runR (Std.Option.reify IR.reify)
             (GT.show Std.Option.ground IR.show)
             (GT.show Std.Option.logic IR.show_logic)
          1 q qh (Printf.sprintf "test_demo: `%s`" (Expr.show e), fun ir ->
            eval_pat (Expr.inject e) injected_pats (ir)
        )
      );
    print_newline ();

    let non_exh_pats = (Expr.econstr "DUMMY" []) :: non_exh_pats in
    (List.map Expr.inject demo_exprs, List.map Expr.inject non_exh_pats)
  in

  runR IR.reify IR.show IR.show_logic n
    q qh ("ideal_IR", fun ideal_IR ->
      let init = success in
      let init =
        List.fold_left (fun acc (scru: Expr.injected) ->
          (eval_ir_hacky scru (fun _ _ _ -> success) ideal_IR (IR.fail()))
        ) init non_exh_pats
      in
      List.fold_left (fun acc (scru: Expr.injected) ->
        fresh (res_pat res_ir)
          acc
          (eval_pat_hacky scru (IR.fail()) injected_pats res_pat)
          (eval_ir_hacky  scru (fun _ _ _ -> failure) ideal_IR      res_ir)
          (res_pat === res_ir)
      ) init injected_exprs
    )



let () =
  let ps =
    [ pnil , IR.eint 1
    ; pwc  , IR.eint 2
    ]
  in
  main ~n:10 ps;
  run_hacky ps

*)

let patterns2 : (Pattern.ground * IR.ground) list =
  (* [ psome pnil, IR.eint 1
  ; psome  pwc, IR.eint 2
  ] *)
  (* [  pwc, IR.eint 1
  ; pnil, IR.eint 2
  ] *)
  [ ppair pnil pwc, IR.eint 1
  ; ppair pwc  pnil, IR.eint 2
  ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 3
  ]
  (*[ ppair pnil pwc,  IR.eint 1
  ; ppair pwc  pnil, IR.eint 2
  ; ppair pnil pnil, IR.eint 3
  ]*)

let eval_with_guards :
  Expr.injected ->
  onfail:IR.injected ->
  ( Nat.injected ->
    Expr.injected ->
    (string * Matchable.ground, (string OCanren.logic, Matchable.logic) Std.Pair.logic) Std.List.groundi ->
    (bool, bool OCanren.logic) OCanren.injected -> goal) ->
  Clauses_with_guards.injected ->
  IR.injected ->
  goal
  = fun s ~onfail eval_guard pats res ->
      eval_with_guards
        ((===)s)
        ((===)onfail)
        (fun a b z -> Fresh.two (fun x y -> (a x) &&& (b y) &&& (eval_guard x y z)))
        ((===)pats)
        res


module TypedLists = struct
(*
match xs,ys with
| [],_ -> ys
| _,[] -> xs
| x::rx,y::ry -> ...
*)
  open Helper
  module GPair = OCanren.Std.Pair

  let inhabit_pair : (*'a 'b 'c 'd.*)
      (('a, 'b) OCanren.injected -> goal) ->
      (('c, 'd) OCanren.injected -> goal) ->
      ('a * 'c, ('b * 'd) OCanren.logic) OCanren.injected ->
      goal
    = fun inh_left inh_right r ->
    conde
      [ fresh (l r)
          (r === Std.pair l r)
          (inh_left l)
          (inh_right r)
      ]

  (** [inhabit_list height arg r] returns all inhabtants of the list where
    list elements are inhabited by [arg] and amount of Nil/Cons constructors
    are equal or less then [height]
  *)
  let rec inhabit_list :
      Std.Nat.groundi ->
      (('a, 'b) OCanren.injected -> goal) ->
      ('a, 'b) Std.List.groundi ->
      goal
    = fun height inh_arg r ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev)
          (Std.Nat.succ prev === height)
          (conde
            [ (r === Std.nil ())
            ; fresh (size_tl h tl)
                (Std.List.cons h tl === r)
                (inh_arg h)
                (inhabit_list prev inh_arg tl)
            ])
      ]

  let () =
    run one (fun q -> fresh (h) (inhabit_list (Std.nat 2) inhabit_free q))
      (fun r -> r#reify (Std.List.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt Std.List.logic @@ (fmt OCanren.logic @@ fmt bool)) x
       )
    |> OCanren.Stream.take ~n:(10) |> ignore;
    Format.printf "\n%!"

  let () =
    run one (fun q -> fresh (h) (inhabit_list (Std.nat 1) inhabit_free q))
      (fun r -> r#reify (Std.List.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt Std.List.logic @@ (fmt OCanren.logic @@ fmt bool)) x
       )
    |> OCanren.Stream.take ~n:(10) |> ignore;
    Format.printf "\n%!"

  (* Testing inhabitants of a pair of two lists *)
  let inhabit_pair_lists :
      Std.Nat.groundi ->
      (('a, 'b) OCanren.injected -> goal) ->
      (_, _) OCanren.injected ->
      goal
    = fun height inh_list_arg rez ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev l r)
          (Std.Nat.succ prev === height)
          (rez === Std.pair l r)
          (inhabit_list prev inh_list_arg l)
          (inhabit_list prev inh_list_arg r)
      ]

  let () =
    let fmt_list = GT.(fmt Std.List.logic (fmt OCanren.logic @@ fmt int)) in
    run one (fun q -> fresh (h) (inhabit_pair_lists (Std.nat 4) inhabit_int q))
      (fun r -> r#reify (Std.Pair.reify (Std.List.reify OCanren.reify) (Std.List.reify OCanren.reify)))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i
          GT.(fmt Std.Pair.logic fmt_list fmt_list)
          x
       )
    |> OCanren.Stream.take ~n:(-1) |> ignore;
    Format.printf "\n%!"

  (*
  For example all lists of <= two elements (height = 4) will be enough

    match xs,ys with
    | [],_ -> ys
    | _,[] -> xs
    | x::rx,y::ry -> ...
  *)

  let run_hacky ?(n=10) (patterns2: (Pattern.ground * (Nat.ground option * IR.ground)) list) on_guard =
    let injected_pats = inject_patterns patterns2 in

    let injected_exprs =
      let demo_exprs =
        let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
        let prjl e =
          Std.List.prjc
            prj1
            (fun _ _ -> failwith "should not happen2")
            e
          in
        let prjp e =
          Std.Pair.prjc
            prjl
            prjl
            (fun _ _ -> failwith "should not happen5")
            e
        in
        run one (fun q -> fresh (h) (inhabit_pair_lists (Std.nat 4) inhabit_int q))
          (fun r -> r#prjc prjp)
        |> OCanren.Stream.take ~n:(-1)
      in
      let demo_exprs =
        let rec hack_list = function
        | Std.List.Nil -> EConstr ("nil", Std.List.Nil)
        | Std.List.Cons (_,tl) ->
            EConstr ("cons", Std.List.of_list id [EConstr ("int", Std.List.Nil); hack_list tl])
        in
        ListLabels.map demo_exprs ~f:(fun (a,b) ->
          EConstr ("pair", Std.List.of_list id [ hack_list a; hack_list b])
        )
      in
      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;
      print_demos "demo_exprs" demo_exprs;
      let () =
        demo_exprs |> List.iter (fun e ->
          print_endline @@ Expr.show e;
          let open OCanren in
          run one (fun ir ->
              (IR.fail () =/= ir) &&&
              (eval_with_guards (Expr.inject e)
                ~onfail:(IR.fail ()) on_guard injected_pats ir))
            (fun r -> r)
            |> (fun s ->
                if OCanren.Stream.is_empty s
                then failwith (Printf.sprintf "can't get any answer")
            )
          )
      in
      List.map Expr.inject demo_exprs
      (*let non_exh_pats = (Expr.econstr "DUMMY" []) :: non_exh_pats in
      (List.map Expr.inject demo_exprs, List.map Expr.inject non_exh_pats)*)
    in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR", fun ideal_IR ->
        let init = success in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_ir)
            acc
            (eval_with_guards scru ~onfail:(IR.fail ()) on_guard injected_pats ideal_IR)
            (eval_ir          scru ~onfail:(IR.fail ()) on_guard               ideal_IR)
          ) init injected_exprs
      );

    Format.printf "%!\n";

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR", fun ideal_IR ->
        let init =
          (*fresh (th el)
            (IR.iftag !!"nil" Matchable.(field (s(z())) (scru())) th el === ideal_IR)*)
            success
        in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (eval_with_guards scru ~onfail:(IR.fail ()) on_guard injected_pats res_ir)
            (eval_ir  scru on_guard ideal_IR      res_ir)
          ) init injected_exprs
      )


  let patterns1 =
    [ ppair pwc  pwc,                 (Some Nat.Z,  IR.eint 100)
    ; ppair pwc  pnil,                       (None,        IR.eint 200)
    ; ppair (pcons pwc pwc) (pcons pwc pwc), (None,        IR.eint 300)
    ]

  let guards1 gndx _ res =
    (Nat.z === gndx) &&& success

  let () =
    let open OCanren in
    let on_guard gndx _ res =
      (Nat.z === gndx) &&& success
    in

    let injected_pats = inject_patterns patterns1 in
    let e = Expr.(econstr "pair" [econstr "nil" []; econstr "nil" []; ]) in

    let () =
      let match_pat_bindings e p r = match_pat_bindings ((===)e) ((===)p) r in
      let injected_pat =
          Pattern.inject @@ ppair (pvar "x") pwc
      in
      runR
        (Std.Option.reify @@ Std.List.reify Expr.reify)
        (GT.show Std.Option.ground @@ GT.show Std.List.ground Expr.show)
        (GT.show Std.Option.logic @@ GT.show Std.List.logic Expr.show_logic)
        1 q qh ("asdf", fun r ->
            (match_pat_bindings (Expr.inject e) injected_pat r))
    in
    runR IR.reify IR.show IR.show_logic
      1 q qh ("asdf", fun ir ->
          (eval_with_guards (Expr.inject e)
            ~onfail:(IR.fail ()) on_guard injected_pats ir))








(*  let () =
    run_hacky ~n:5
      [ ppair pnil  pwc, (None, IR.eint 1)
      ; ppair pwc  pnil, (None, IR.eint 2)
      ; ppair (pcons pwc pwc) (pcons pwc pwc), (None, IR.eint 3)
      ]
      (fun _ _ res -> failure)*)

(*  let () =
    run_hacky ~n:5 patterns1 guards1*)

end
