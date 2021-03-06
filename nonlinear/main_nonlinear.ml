module Work = Work_nonlinear
open Printf
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

module Pattern = struct
  type ('a,'b) t = ('a,'b) Work.gpattern =
    WildCard | PVar of 'a | PConstr of 'a * 'b
    [@@deriving gt ~options:{fmt; gmap}]

  type ground = (string, ground Std.List.ground) t
  type logic = (string OCanren.logic, logic Std.List.logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = pConstr
  let wc = wildCard
  let var = pVar

  let rec height = function
  | WildCard  -> 0
  | PConstr (_,ps) ->
    GT.foldl Std.List.ground (fun acc x -> max acc (height x)) 0 ps + 1

  let ground_list_length xs =
    GT.foldl Std.List.ground (fun acc _ -> acc+1) 0 xs

  let show p =
    let rec helper = function
    | WildCard -> "_"
    | PConstr (s, Std.List.Nil) -> Printf.sprintf "(%s)" s
    | PConstr (s, ps) ->
      Printf.sprintf "(%s %s)" s (GT.show Std.List.ground helper ps)
    in
    helper p

  let rec show_logic (p: logic) =
    let rec helper = function
    | WildCard -> "_"
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



  module ArityMap = Map.Make(Base.String)
  exception Bad

  let get_arities (pat: ground) =
    let rec helper acc = function
      | WildCard -> acc
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

(* TODO: put this to stdlib *)
let rec inject_ground_list ps =
  (* TODO: tail recursion *)
  let rec helper = function
  | Std.List.Nil -> Std.List.nil ()
  | Std.List.Cons (x, xs) -> Std.List.cons x (helper xs)
  in
  helper ps


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

  (* let rec populate_lists length (orig: 'a list) : 'a list list =
    Printf.printf "populate_lists length=%d\n%!" length;
    let rec helper n =
      if n<1 then failwith (Printf.sprintf "populate_list: bad argument %d" n)
      else if n=1 then [orig]
      else
        let prevs = helper (n-1) in
        List.iter (fun xs -> assert (length = (List.length xs))) prevs;
        List.flatten @@
        List.map (fun tl -> List.map (fun h -> h::tl) orig) prevs
    in
    let ans = helper length in
    List.iter (fun xs -> assert (length = (List.length xs))) ans;
    ans
  in *)


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
(*
let checkAnswer = eval_ir

let _ =
  run_exn (Format.asprintf "%a" (pp_maybe pp_rhs)) 1 q qh ("answers", fun q ->
    checkAnswer (pair (leaf "aaa") (leaf "bbb"))
      (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
      q
  )

let _foo () =
  runR Expr.reify Expr.show Expr.show_logic
        1 q qh ("answers", fun q ->
     checkAnswer
        q
        (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
        (Std.some (!!2))
  )

*)
let add_freshes n pregoal =
  let rec helper acc n =
    if n = 0 then pregoal acc
    else OCanren.Fresh.one (fun q -> helper (q::acc) (n-1))
  in
  helper [] n

let pwc = WildCard
let pconstr name xs = PConstr (name, Std.List.of_list id xs)
let pleaf s = pconstr s []
let pnil    = pleaf "nil"
let pcons a b = pconstr "cons" [a;b]
let psome a   = pconstr "some" [a]
let ppair a b : Pattern.ground = pconstr "pair" [a;b]

(* let patterns1 : Pattern.ground list =
  [ ppair pnil pwc
  ; ppair pwc  pnil
  ; ppair (pcons pwc pwc) (pcons pwc pwc)
  ] *)


(* let _ =
  runR Expr.reify Expr.show Expr.show_logic 10
    q qh ("answers", make_expr_generator patterns1) *)

let (>>=?) x f = match x with None -> None | Some x -> f x

module Nat = struct
  type 'a gnat = 'a Work.gnat = Z | S of 'a [@@deriving gt ~options:{fmt}]
  type ground = ground gnat
  type logic = logic gnat OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let z : injected = Work.z ()
  let one : injected =  Work.s z
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

  let rec reify env x = For_gnat.reify reify env x

  let rec to_ground = function
    | Var (_,_) -> None
    | Value (Z) -> Some Z
    | Value (S x) -> to_ground x >>=? fun x -> Some (S x)
end

module Matchable = struct
  type ground = (Nat.ground, ground) gmatchable
  type logic = (Nat.logic, logic) gmatchable OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let scru = scru
  let field = field

  let field0  () = field (z())    @@ scru()
  let field1  () = field (s(z())) @@ scru()
  let field00 () = field (z())    @@ field0 ()
  let field01 () = field (s(z())) @@ field0 ()
  let field10 () = field (z())    @@ field1 ()
  let field11 () : injected = field (s(z())) @@ field1 ()

  let rec reify env x =
    For_gmatchable.reify Nat.reify reify env x

  let rec show_logic x =
    let rec helper = function
    | Scru        -> "S"
    | Field (n,r) ->
      Printf.sprintf "%s[%s]" (show_logic r) (Nat.show_logic n)
    in
    GT.show OCanren.logic helper x

  let show x =
    let rec helper = function
    | Scru        -> "S"
    | Field (n,r) -> Printf.sprintf "%s[%s]" (helper r) (Nat.show n)
    in
    helper x

  let to_ground l =
    let rec helper = function
    | Value Scru -> Some Scru
    | Value (Field (n, m)) ->
        Nat.to_ground n >>=? fun n ->
        helper m        >>=? fun m ->
        Some (Field (n,m))
    | Var (_,_) -> None
    in
    helper l
end


module IR = struct
  type ground = (int, string, Matchable.ground, ground) gir
  type logic = (int OCanren.logic, string OCanren.logic, Matchable.logic, logic) gir OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let fail = fail
  let iftag = iFTag
  let int = int

  let eint n = Int n

  let rec reify env x : logic =
    For_gir.reify  OCanren.reify OCanren.reify Matchable.reify reify env x

  let inject e =
    let rec helper = function
    | Int n -> int !!n
    | _ -> failwith "not implemented"
    in
    helper e

  let show e =
    let rec helper = function
    | Fail -> "(fail)"
    | Int n -> string_of_int n
    | IFTag (str, m, th, el) ->
      let str = if str = "nil" then " nil" else str in
      Printf.sprintf "(iftag %S %s %s %s)"
        str
        (Matchable.show m)
        (helper th)
        (helper el)
    | IFEq (a,b,th,el) ->
        Printf.sprintf "(ifeq %s %s %s %s)"
          (Matchable.show a)
          (Matchable.show b)
          (helper th)
          (helper el)
    in
    helper e

  let show_ocl f = GT.show OCanren.logic f
  let show_ocl_small f = function
    | Value x -> f x
    | Var (n,_) -> Printf.sprintf "_.%d" n

(*  let show_ocl_small = show_ocl     (* PRINTING HACK *)*)

  let rec show_logic (e: logic) =
    let rec helper = function
    | Fail -> "(fail)"
    | Int ln -> show_ocl_small (GT.show GT.int) ln
    | IFTag (ltag, m, th, el) ->
      Printf.sprintf "(iftag %s %s %s %s)"
        (show_ocl_small (fun s -> sprintf "\"%s%s\"" (if String.length s = 3 then " " else "") s) ltag)
        (Matchable.show_logic m)
        (show_logic th)
        (show_logic el)
    | IFEq (a,b,th,el) ->
      Printf.sprintf "(ifeq %s %s %s %s)"
        (Matchable.show_logic a)
        (Matchable.show_logic b)
        (show_logic th)
        (show_logic el)
    in
    show_ocl_small helper e
end


module Clauses = struct
  type ground = (Pattern.ground * IR.ground) Std.List.ground
  type logic = (Pattern.logic, IR.logic) Std.Pair.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected
end

let eval_m : Expr.injected -> IR.injected -> Clauses.injected -> IR.injected -> goal =
  eval_pat_hacky

let inject_patterns ps =
  let rec one : Pattern.ground -> _ = function
  | WildCard -> Pattern.wc ()
  | PVar s -> pVar !!s
  | PConstr (name,ps) ->
      Pattern.constr !!name @@
      (inject_ground_list @@ GT.gmap Std.List.ground one ps)
  in

  Std.List.list @@
  List.map (fun (p,rhs) -> Std.Pair.pair (one p) (IR.inject rhs)) ps


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
      (*left_desc: Info.inj ->
      right_desc: Info.inj ->*)
      ('a * 'c, ('b * 'd) OCanren.logic) OCanren.injected ->
      goal
    = fun inh_left inh_right r ->
    conde
      [ fresh (l r)
          (r === Std.pair l r)
          (inh_left l)
          (inh_right r)
      ]


  (*
  For example all lists of <= two elements (height = 4) will be enough

    match xs,ys with
    | [],_ -> ys
    | _,[] -> xs
    | x::rx,y::ry -> ...
  *)

  let run_hacky ?examples ?(n=10) patterns2 =
    let injected_pats = inject_patterns patterns2 in

    let injected_exprs =
      let demo_exprs =
        match examples with
        | Some xs -> xs
        | None -> []
      in
      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;
      let () =
        demo_exprs |> List.iter (fun e ->
          print_endline @@ Expr.show e;
          let open OCanren in
          run one (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  print_endline @@ IR.show_logic  ((OCanren.Stream.hd s)#reify IR.reify);
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

(*
    let rec my_eval_m s h ans =
      conde
        [ (h === (scru ())) &&& (s === ans) &&& (fresh (a b) (Expr.constr !!"pair" Std.(a %< b) === ans))
        ; fresh (n m q23 cname es)
            (* field of scrutineee *)
            (scru () === m)
            (h === (field n m))
            (conde [  n === (Nat.s (z())); n === z () ])
            (q23 === (eConstr cname es))
            (list_nth_nat n es ans)
            (my_eval_m s m q23)

        ; fresh (n m q23 q24 es)
            (h === (field n m))
            (m =/= scru())
            (conde [ n === z (); n === (Nat.s (z())) ])
            (q23 === (eConstr q24 es))
            (list_nth_nat n es ans)
            (my_eval_m s m q23)
        ]
    in

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s ir ans =
      conde
        [ (ir === (fail ())) &&& (ans === (none ()))
        ; fresh (n)
            (ir === (int n))
            (ans === (some n))
        (*; Fresh.one @@ fun n ->
            (ir === (int n)) &&&
            (ans === (some n))*)

        ; fresh (tag scru2 th el q14 tag2 args q16 q6)
            (ir === (iFTag tag scru2 th el))
            (q14 === (eConstr tag2 args))
            (my_eval_m s scru2 q14)

            (* Commenting next goal leads to no answers *)

            (let open Matchable in
             conde
              [ (scru2 === scru   ()) &&& failure
              ; (scru2 === field0 ()) &&&
                (conde [ tag === !!"nil"; tag === !!"cons" ]) &&&
                (conde
                  [ (make_constraint2 el (Field (Z,Scru)) ) &&&
                    (make_constraint2 th (Field (Z,Scru)) )
                  ])
              ; (scru2 === field1 ()) &&&
                (conde [ tag === !!"nil"; tag === !!"cons" ]) &&&
                (conde
                  [ (make_constraint2 el (Field (S Z,Scru)) ) &&&
                    (make_constraint2 th (Field (S Z,Scru)) )
                  ])
              ; (scru2 === field00()) &&& failure
              ; (scru2 === field01()) &&& failure
              ; (scru2 === field10()) &&& failure
              ; (scru2 === field11()) &&& failure
              ])

            (conde
               [ (tag2 === tag) &&& (self s th ans)
               ; (tag2 =/= tag) &&& (self s el ans)
               ])
        ]
      in
      (fun a b c ->
        (height_hack ideal) &&&
        (Tabling.(tabledrec three) inner a b c)
      )
    in
*)
    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR", fun ideal_IR ->
        let init = success in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (eval_pat             scru injected_pats res_pat)

            (conde
              [ fresh (n)
                 (res_pat === Std.Option.some (IR.int n))
                 (res_ir  === Std.Option.some n)
              ; (res_pat === Std.Option.none ()) &&& (res_ir === Std.Option.none())
              ])
            (eval_ir  scru ideal_IR      res_ir)
          )
          init
          injected_exprs
      );

    Format.printf "%!\n";

    ()

  let () =
    let a : Pattern.ground = pconstr "A" [] in
    let b : Pattern.ground = pconstr "B" [] in
    let pvar s : Pattern.ground = PVar s in

    let examples1 =
      let a = EConstr ("A", Std.List.of_list id []) in
      let b = EConstr ("B", Std.List.of_list id []) in
      [ EConstr ("pair", Std.List.of_list id [a; a;])
      ; EConstr ("pair", Std.List.of_list id [b; a;])
      ; EConstr ("pair", Std.List.of_list id [a; b;])
      ; EConstr ("pair", Std.List.of_list id [b; b;])
      ]
    in
    run_hacky ~examples:examples1 ~n:2
      [ ppair a a, IR.eint 10
      ; ppair pwc pwc, IR.eint 30
      ];
    run_hacky ~examples:examples1 ~n:2
      [ (pvar "x") , IR.eint 10
      ; pwc, IR.eint 30
      ];
    run_hacky ~examples:examples1 ~n:2
      [ ppair (pvar "x") (pvar "x"), IR.eint 10
      ; ppair pwc pwc, IR.eint 30
      ];
    ()

end
