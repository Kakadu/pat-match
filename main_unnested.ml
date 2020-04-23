module Work = Work_unnested
open Printf
open Work
open OCanren
open Mytester

exception FilteredOut

let id x = x

let pp_rhs fmt = Format.fprintf fmt "%d"
let pp_maybe fa fmt = function
| None -> Format.fprintf fmt "None"
| Some x -> Format.fprintf fmt "(Some %a)" fa x

let leaf s = eConstr !!s @@ Std.List.nil ()
let pair a b = eConstr !!"pair" (Std.List.list [a;b])

module Pattern = struct
  type ('a,'b) t = ('a,'b) Work.gpattern = WildCard | PConstr of 'a * 'b
    [@@deriving gt ~options:{fmt; gmap}]

  type ground = (string, ground Std.List.ground) t
  type logic = (string OCanren.logic, logic Std.List.logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = pConstr
  let wc = wildCard

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

let checkAnswer = eval_ir

(*
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
let pnil2   = pleaf "nil2"
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
  type 'a gnat = 'a Work.gnat = Z | S of 'a [@@deriving gt ~options:{fmt; foldl}]
  type ground = ground gnat [@@deriving gt ~options:{fmt; foldl}]
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

  let inject : ground -> injected = fun root ->
    let rec helper = function
    | Z -> z
    | S p -> s @@ helper p
    in
    helper root

  let rec to_ground = function
    | Var (_,_) -> None
    | Value (Z) -> Some Z
    | Value (S x) -> to_ground x >>=? fun x -> Some (S x)
end

module Matchable = struct
  type ('a1, 'a0) gmatchable = ('a1, 'a0) Work.gmatchable =
    | Scru
    | Field of 'a1 * 'a0
    [@@deriving gt ~options:{ foldl }]
  type ground = (Nat.ground, ground) gmatchable
    [@@deriving gt ~options:{ foldl }]
  type logic = (Nat.logic, logic) gmatchable OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let scru = scru
  let field = field

  let field0  () = field (z())    @@ scru()
  let field1  () = field (s(z())) @@ scru()
  let field00 () = field (z())    @@ field0 ()
  let field01 () = field (s(z())) @@ field0 ()
  let field10 () = field (z())    @@ field1 ()
  let field11  () : injected = field (s(z())) @@ field1 ()

  let field000 () : injected = field (z())    @@ field00 ()
  let field001 () : injected = field (z())    @@ field01 ()
  let field010 () : injected = field (z())    @@ field10 ()
  let field011 () : injected = field (z())    @@ field11 ()
  let field100 () : injected = field (s(z())) @@ field00 ()
  let field101 () : injected = field (s(z())) @@ field01 ()
  let field110 () : injected = field (s(z())) @@ field10 ()
  let field111 () : injected = field (s(z())) @@ field11 ()

  let rec reify env x =
    For_gmatchable.reify Nat.reify reify env x

  let inject : ground -> injected = fun root ->
    let rec helper = function
    | Scru -> scru ()
    | Field (n, prev) -> field (Nat.inject n) (helper prev)
    in
    helper root

  let height_ground m : int =
    GT.transform ground
      (fun fself -> object
        inherit [_,_] foldl_ground_t fself
        method m_Scru acc _ = acc+1
        method m_Field acc _ _ prev = fself (acc+1) prev
      end)
     0
     m

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
  (*type nonrec ('a3, 'a2, 'a1, 'a0) gir = ('a3, 'a2, 'a1, 'a0) Work.gir  =
  | Fail
  | IFTag of 'a3 * 'a2 * 'a1 * 'a1
  | Int of 'a0*)

  type ground = (string, Matchable.ground, ground, int) gir
  type logic = (string OCanren.logic, Matchable.logic, logic, int OCanren.logic) gir OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let fail = fail
  let iftag = iFTag
  let int = int

  let eint n = Int n

  let rec reify env x =
    For_gir.reify OCanren.reify Matchable.reify reify OCanren.reify env x

  let inject e =
    let rec helper = function
    | Int n -> int !!n
    | Fail -> fail ()
    | IFTag (str, matchable, th, el) ->
      iftag !!str (Matchable.inject matchable) (helper th) (helper el)
    | _ -> failwith "not implemented"
    in
    helper e

  let show e =
    let rec helper = function
    | Fail -> "(fail)"
    | Int n -> string_of_int n
    | IFTag (str, m, th_, el_) ->
      let str = if str = "nil" then " nil" else str in
      Printf.sprintf "(iftag %S %s %s %s)"
        str
        (Matchable.show m)
        (helper th_)
        (helper el_)
    in
    helper e

  let show_ocl f = GT.show OCanren.logic f
  let show_ocl_small f = function
    | Value x -> f x
    | Var (n,_) -> Printf.sprintf "_.%d" n

  let show_ocl_small = show_ocl     (* PRINTING HACK *)

  let rec show_logic e =
    let rec helper = function
    | Fail -> "(fail)"
    | Int ln -> show_ocl_small (GT.show GT.int) ln
    | IFTag (ltag, m, th_, el_) ->
      Printf.sprintf "(iftag %s %s %s %s)"
        (show_ocl (fun s -> sprintf "\"%s%s\"" (if String.length s = 3 then " " else "") s) ltag)
        (Matchable.show_logic m)
        (show_logic th_)
        (show_logic el_)
(*    | _ -> Printf.sprintf "<logic ir>"*)
    in
    show_ocl_small helper e
end


module Clauses = struct
  type pg = Pattern.ground * IR.ground
  type ground = pg Std.List.ground
  type logic = (Pattern.logic, IR.logic) Std.Pair.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected

  let inject : pg list -> injected = fun ps ->
    let rec one : Pattern.ground -> _ = function
    | WildCard -> Pattern.wc ()
    | PConstr (name,ps) ->
        Pattern.constr !!name @@
        (inject_ground_list @@ GT.gmap Std.List.ground one ps)
    in

    Std.List.list @@
    List.map (fun (p,rhs) -> Std.Pair.pair (one p) (IR.inject rhs)) ps


end


module TypedLists = struct
  (*
  match xs,ys with
  | [],_ -> ys
  | _,[] -> xs
  | x::rx,y::ry -> ...
  *)
  open Helper


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

  let _comment () =
    run one (fun q -> fresh (h) (inhabit_list (Std.nat 2) inhabit_free q))
      (fun r -> r#reify (Std.List.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt Std.List.logic @@ (fmt OCanren.logic @@ fmt bool)) x
       )
    |> OCanren.Stream.take ~n:(10) |> ignore;
    Format.printf "\n%!"

  let _comment () =
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

  let _comment () =
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



  let run_hacky ?(n=10) clauses  =
    let injected_pats = Clauses.inject clauses in

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
(*      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;*)
(*      print_demos "demo_exprs" demo_exprs;*)
      let () =
        demo_exprs |> List.iter (fun e ->
(*          print_endline @@ Expr.show e;*)
          let open OCanren in
          run one (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
(*                  let (_:int)  = (OCanren.Stream.hd s) in*)
(*                  print_endline @@ IR.show_logic  ((OCanren.Stream.hd s)#reify IR.reify);*)
            )
          )
      in
      List.map Expr.inject demo_exprs
      (*let non_exh_pats = (Expr.econstr "DUMMY" []) :: non_exh_pats in
      (List.map Expr.inject demo_exprs, List.map Expr.inject non_exh_pats)*)
    in

    let count_constructors : IR.logic -> int = fun root ->
      let rec helper = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (_,scrul,then_,else_)) ->
          let scru_mb = Matchable.to_ground scrul in
          let () =
            match scru_mb with
            | Some scru_ground ->
              if (Matchable.height_ground scru_ground > 2) then raise FilteredOut
            | None -> ()
          in
          let a = helper then_ in
          let b = helper else_ in
          (1+a+b)
      in
      helper root
    in
    let height_hack ans =
      let max_ifs_count = 2 in (* TODO: populated for simple example *)
      let do_debug = false  in
      structural ans IR.reify (fun ir ->
        let debug fmt =
          Format.ksprintf (fun s -> if do_debug then Format.printf "%s" s else ())
            fmt
        in
        try
          debug "height_hack `%s` = %!" (IR.show_logic ir);
          let n = count_constructors ir in
          debug "%d%!" n;
          match n with
          | x when x>2 -> raise FilteredOut
          | _ ->
              debug "\n%!";
              true
        with FilteredOut ->
          debug " FILTERED OUT\n%!";
          false
      )
    in

(*
    let costf : IR.logic -> OCanren.cost = fun root ->
      let rec helper (low,var) = function
      | Var (_,_)     -> (low,true)
      | Value (Int _)
      | Value (Fail)  -> (0,false)
      | Value (IFTag (_,_,then_,else_)) ->
          let (lw,lf) = helper (0,false) then_ in
          let (rw,rf) = helper (0,false) else_ in
          (lw+rw+1, lf || rf)
      in
      let (n,has_var) = helper (0,false) root in
(*      Format.printf "costing `%s` = %d\n%!" (IR.show_logic root) n;*)
      let n = if n < 3 then 3 else n in
      if has_var
      then OCanren.CAtLeast n
      else OCanren.CFixed n
    in
*)

    let rec list_nth_nat idx xs ans =
      conde
        [ fresh (prev h tl)
            (Nat.one === idx)
            (xs === Std.(h % (ans % tl)))
        ; fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ]
    in

    let rec my_eval_m s h ans =
      conde
        [ (h === (scru ())) &&& (s === ans) &&& (fresh (a b) (Expr.constr !!"pair" Std.(a %< b) === ans))
        ; fresh (n m q23 cname es)
            (* field of scrutineee *)
            (scru () === m)
            (h === (field n m))
            (conde [  n === (Nat.s (z())); n === z () ])

(*            (conde
              [ cname === !!"nil"  &&&              (es === Std.nil())
              ; cname === !!"cons" &&& (fresh (a b) (es === Std.(a %< b)))
              ])*)

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

    let make_constraint var scru tag =
      (* we should not see the code which tests scru for this constructor *)
      structural var IR.reify (fun ir ->
        (*Format.printf "structural of '%s' with cname=%a and scru = %s\n"
          (IR.show_logic ir)
          (GT.fmt GT.string) tag
          (Matchable.show scru);*)

        let fail = false in
        let ok = true in
        let rec helper ir =
          match ir with
          | Var (_,_) -> ok
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru) && (_c = tag)
              then fail
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in
    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var IR.reify (fun ir ->
(*        Format.printf "structural2 of '%s' with scru = %s\n"
          (IR.show_logic ir)
          (Matchable.show scru);*)

        let rec helper ir =
          match ir with
          | Var (_,_) -> true
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru)
              then false
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

(*    let trace_tag tag =
      structural tag OCanren.reify (fun tag ->
        Format.printf "trace_var %s\n" (GT.show(OCanren.logic) (GT.show(GT.string)) tag);
        true
      )
    in*)

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s ir ans =
        let make_constraints_goal tag ~th ~el scru2 =
          let open Matchable in
          let wrap tag_str scur_g =
(*             (tag === !!tag_str) &&&*)
             (make_constraint th scur_g tag_str) &&&
             (make_constraint el scur_g tag_str)
          in
          conde
            [ (scru2 === scru   ()) &&& failure
            ; (scru2 === field0 ())

              (*&&& (wrap "nil"  (Field (Z,Scru)) )
              &&& (wrap "cons" (Field (Z,Scru)) )*)
              &&& (conde [ tag === !!"nil"; tag === !!"cons" ])
(*              &&& (make_constraint2 el (Field (Z,Scru)) )
              &&& (make_constraint2 th (Field (Z,Scru)) )*)


            ; (scru2 === field1 ())
              (*&&& (wrap "nil"  (Field (S Z,Scru)) )
              &&& (wrap "cons" (Field (S Z,Scru)) )*)
              &&& (conde [ tag === !!"nil"; tag === !!"cons" ])
(*              &&& (make_constraint2 el (Field (S Z,Scru)))
              &&& (make_constraint2 th (Field (S Z,Scru)))*)


            ; (scru2 === field00()) &&& failure
            ; (scru2 === field01()) &&& failure
            ; (scru2 === field10()) &&& failure
            ; (scru2 === field11()) &&& failure
            ]
        in
        conde
          [ (ir === (fail ())) &&& (ans === (none ()))
          ; fresh (n)
              (ir === (int n))
              (ans === (some n))

          ; fresh (tag scru2 th el q14 tag2 args q16 q6)
              (ir === (iFTag tag scru2 th el))
(*              (trace_tag tag)*)
              (q14 === (eConstr tag2 args))
              (conde [scru2 === scru   (); scru2 === Matchable.field0 ();  scru2 === Matchable.field1 () ])
              (my_eval_m s scru2 q14)

              (conde
                 [ (tag =/= tag2) &&&
(*                   (make_constraints_goal ~th ~el tag scru2) &&&*)
                   (self s el ans)
                 ; (tag === tag2) &&&
(*                   (make_constraints_goal ~th ~el tag scru2) &&&*)
                   (self s th ans)
                 ])
          ]
      in
      (fun a b c ->
        (height_hack ideal) &&&
        (*
        let rec y f x = f (fun z -> y f  z) x in
        y inner a b c
        *)
        (Tabling.(tabledrec three) inner a b c)
      )
    in

    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR 0 with hacks ", (fun ideal_IR ->
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
            (my_eval_ir  ideal_IR scru ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));

    Format.printf "%!\n";
    ()


  (*
  For example all lists of <= two elements (height = 4) will be enough

    match xs,ys with
    | [],_ -> 10
    | _,[] -> 20
    | x::rx,y::ry -> 30
  *)

  let pattern_example1 =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 20
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 30
    ]

  let possible_answer =
    let run_ground clauses : IR.ground =
      let injected : Clauses.injected = Clauses.inject clauses in
      let first =
        OCanren.(run q (compile_naively injected)) (fun rr -> rr#prj)
        |> Stream.hd
      in
      print_endline "naive answer:";
      print_endline @@ IR.show first;
      let rec optimize (root: IR.ground)  =
        let rec helper = function
          | IFTag ("pair", Scru, then_, _) -> optimize then_
          | IFTag (c, scru, then_, else_) ->
              IFTag (c, scru, optimize then_, optimize else_)
          | x -> x
        in
        helper root
      in
      let second = optimize first in
      print_endline "\noptimized answer:";
      print_endline @@ IR.show @@ second;
      second
    in
    run_ground pattern_example1


  let _f  =
    run_hacky ~n:(10)
      pattern_example1

end



module Typs = struct
  type 'a t = 'a Work.gtyp_info = T of 'a
    [@@deriving gt ~options: { show; fmt }]
  type ground = (GT.string,             ground Std.List.ground) Std.Pair.ground  Std.List.ground t
    [@@deriving gt ~options: { show; fmt }]
  type logic  = (GT.string OCanren.logic, logic Std.List.logic) Std.Pair.logic   Std.List.logic t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let t eta = Work.t eta
  let t_item name xs = Std.Pair.pair name xs

  let rec inject (e: ground) : injected =
    let rec helper : string * ground Std.List.ground -> _ = function
    | (s, xs) ->
        t_item !!s (inject_ground_list @@ GT.gmap Std.List.ground inject xs)
    in
    match e with
    | T xs -> t (inject_ground_list @@ GT.gmap Std.List.ground helper xs)

  let mkt xs: ground = T (Std.List.of_list id xs)

  let rec construct root : ground =
    match root with
    | T xs -> mkt @@ List.map (fun (p,xs) -> (p, Std.List.of_list construct xs)) xs
end

let typs0 =
  let ints = T [ ("1",[]) ] in
  let list_empty = T [  ("nil", []);  ] in
  let listints1 = T [ ("nil", []);  ("cons", [ ints; list_empty]) ] in
  let listints2 = T [ ("nil", []);  ("cons", [ ints; listints1]) ] in
  let pairs = T [ ("pair", [ listints2; listints2]) ] in
  let grounded = Typs.construct pairs in
  Typs.inject grounded

(*
(* Two nil lists types *)
let typs1 =
  let ints = T [ ("1",[]) ] in
  let list_empty = T [  ("nil", []); ("nil2", []) ] in
  let listints1 = T [ ("nil", []); ("nil2",  []); ("cons", [ ints; list_empty]) ] in
  let listints2 = T [ ("nil", []); ("nil2", []); ("cons", [ ints; listints1]) ] in
  let pairs = T [ ("pair", [ listints2; listints2]) ] in
  let grounded = Typs.construct pairs in

(*  Format.printf "types: %s\n%!" (GT.show Typs.ground grounded);*)
  Typs.inject grounded
*)

module List2 = struct

  let inhabit_pair_lists = TypedLists.inhabit_pair_lists
  let inhabit_int = Helper.inhabit_int

  let run_hacky ?(n=10) clauses typs =
    let injected_pats = Clauses.inject clauses in

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
  (*      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;*)
  (*      print_demos "demo_exprs" demo_exprs;*)
      let () =
        demo_exprs |> List.iter (fun e ->
(*          print_endline @@ Expr.show e;*)
          let open OCanren in
          run one (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
(*                  print_endline @@ IR.show_logic  ((OCanren.Stream.hd s)#reify IR.reify);*)
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

    let count_constructors : IR.logic -> int = fun root ->
      let rec helper = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (_,scrul,then_,else_)) ->
          let scru_mb = Matchable.to_ground scrul in
          let () =
            match scru_mb with
            | Some scru_ground ->
              if (Matchable.height_ground scru_ground > 2) then raise FilteredOut
            | None -> ()
          in
          let a = helper then_ in
          let b = helper else_ in
          (1+a+b)
      in
      helper root
    in
    let height_hack ans =
      let max_ifs_count = 2 in (* TODO: populated for simple example *)
      let do_debug = false  in
      structural ans IR.reify (fun ir ->
        let debug fmt =
          Format.ksprintf (fun s -> if do_debug then Format.printf "%s" s else ())
            fmt
        in
        try
          debug "height_hack `%s` = %!" (IR.show_logic ir);
          let n = count_constructors ir in
          debug "%d%!" n;
          match n with
          | x when x>2 -> raise FilteredOut
          | _ ->
              debug "\n%!";
              true
        with FilteredOut ->
          debug " FILTERED OUT\n%!";
          false
      )
    in

(*
    let rec list_nth_nat idx xs ans =
      conde
        [ fresh (prev h tl)
            (Nat.one === idx)
            (xs === Std.(h % (ans % tl)))
        ; fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ]
    in

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
*)
    let make_constraint var scru tag =
      (* we should not see the code which tests scru for this constructor *)
      structural var IR.reify (fun ir ->
        (*Format.printf "structural of '%s' with cname=%a and scru = %s\n"
          (IR.show_logic ir)
          (GT.fmt GT.string) tag
          (Matchable.show scru);*)

        let fail = false in
        let ok = true in
        let rec helper ir =
          match ir with
          | Var (_,_) -> ok
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru) && (_c = tag)
              then fail
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in
    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var IR.reify (fun ir ->
  (*        Format.printf "structural2 of '%s' with scru = %s\n"
          (IR.show_logic ir)
          (Matchable.show scru);*)

        let rec helper ir =
          match ir with
          | Var (_,_) -> true
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru)
              then false
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s tinfo ir ans =
(*
        let make_constraints_goal tag ~th ~el scru2 =
          let open Matchable in
          let wrap tag_str scur_g =
  (*             (tag === !!tag_str) &&&*)
             (make_constraint th scur_g tag_str) &&&
             (make_constraint el scur_g tag_str)
          in
          conde
            [ (scru2 === scru   ()) &&& failure
            ; (scru2 === field0 ())

              (*&&& (wrap "nil"  (Field (Z,Scru)) )
              &&& (wrap "cons" (Field (Z,Scru)) )*)
              &&& (conde [ tag === !!"nil"; tag === !!"cons" ])
  (*              &&& (make_constraint2 el (Field (Z,Scru)) )
              &&& (make_constraint2 th (Field (Z,Scru)) )*)


            ; (scru2 === field1 ())
              (*&&& (wrap "nil"  (Field (S Z,Scru)) )
              &&& (wrap "cons" (Field (S Z,Scru)) )*)
              &&& (conde [ tag === !!"nil"; tag === !!"cons" ])
  (*              &&& (make_constraint2 el (Field (S Z,Scru)))
              &&& (make_constraint2 th (Field (S Z,Scru)))*)


            ; (scru2 === field00()) &&& failure
            ; (scru2 === field01()) &&& failure
            ; (scru2 === field10()) &&& failure
            ; (scru2 === field11()) &&& failure
            ]
        in
*)
        conde
          [ (ir === (fail ())) &&& (ans === (none ()))
          ; fresh (n)
              (ir === (int n))
              (ans === (some n))

          ; fresh (tag scru th el q27 q33 tag2 args q29 possible_names)
              (ir === (iFTag tag scru th el))
              (q27 === (eConstr tag2 args))
              (Work.eval_m s tinfo scru q33)
              (q33 === Std.Pair.pair q27 possible_names)
              (Std.List.membero possible_names tag)
              (conde [(tag2 === tag) &&& (q29 === (!! true)); (q29 === (!! false)) &&& (tag2 =/= tag)])
              (conde
                [ (q29 === (!! true)) &&& (self s tinfo th ans)
                ; (q29 === (!! false)) &&& (self s tinfo el ans)
                ])
          ]
      in
      (fun a b c d ->
        (height_hack ideal) &&&
        (*
        let rec y f x = f (fun z -> y f  z) x in
        y inner a b c
        *)
        (Tabling.(tabledrec four) inner a b c d)
      )
    in

    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR no hacks ", (fun ideal_IR ->
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
            (my_eval_ir  ideal_IR scru typs ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));

    Format.printf "%!\n";
    ()

  let _f  =
    run_hacky ~n:(2)
      TypedLists.pattern_example1 typs0

end

(*
module TwoNilList = struct
  open Helper

  module TwoNilList = struct
    type ('a, 'self) t = Nil | Nil2 | Cons of 'a * 'self
      [@@deriving gt ~options:{show;fmt; gmap}]
    type 'a ground = ('a, 'a ground) t
      [@@deriving gt ~options:{show;fmt; gmap}]
    type 'a logic = ('a, 'a logic) t OCanren.logic
      [@@deriving gt ~options:{show;fmt; gmap}]
    type ('a, 'b) injected = ('a ground, 'b logic) OCanren.injected

    module T = Fmap2(struct
      type nonrec ('a, 'b) t = ('a, 'b) t
      let fmap fa fb = (GT.gmap t) fa fb
    end)
    let nil  () = inj @@ T.distrib Nil
    let nil2 () = inj @@ T.distrib Nil2
    let cons x xs = inj @@ T.distrib @@ Cons (x,xs)

    let rec reify r1 h = T.reify r1 (reify r1) h


    let rec prjc fa onvar env xs = T.prjc fa (prjc fa onvar) onvar env xs
  end
  module L = TwoNilList

  let rec inhabit_twonil_list :
    Std.Nat.groundi ->
    (('a, 'b) OCanren.injected -> goal) ->
    ('a, 'b) L.injected ->
    goal
  = fun height inh_arg r ->
  conde
    [ (Std.Nat.zero === height) &&& failure
    ; fresh (prev)
        (Std.Nat.succ prev === height)
        (conde
          [ (r === L.nil ())
          ; (r === L.nil2 ())
          ; fresh (size_tl h tl)
              (L.cons h tl === r)
              (inh_arg h)
              (inhabit_twonil_list prev inh_arg tl)
          ])
    ]

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
          (inhabit_twonil_list prev inh_list_arg l)
          (inhabit_twonil_list prev inh_list_arg r)
      ]

  let two_nil_demo_clauses1 =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 20
    ; ppair pnil2 pwc, IR.eint 40
    ; ppair pwc pnil2, IR.eint 50
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 30
    ]



  let possible_answer : IR.ground =
    let run_ground clauses : IR.ground =
      let injected : Clauses.injected = Clauses.inject clauses in

      let first =
        OCanren.(run q (compile_naively injected)) (fun rr -> rr#prj)
        |> Stream.hd
      in
      print_endline "naive answer:";
      print_endline @@ IR.show first;
      let rec optimize (root: IR.ground)  =
        let rec helper = function
          | IFTag ("pair", Scru, then_, _) -> optimize then_
          | IFTag (c, scru, then_, else_) ->
              IFTag (c, scru, optimize then_, optimize else_)
          | x -> x
        in
        helper root
      in
      let second = optimize first in
      print_endline "\noptimized answer:";
      print_endline @@ IR.show @@ second;
      second
    in
    run_ground two_nil_demo_clauses1

  exception FilteredOut

  let synth_twonillist ?(n=10) clauses =
    let check_scrutinee root =
      let rec helper len = function
      | Value Scru -> len+1
      | Value (Field (_, next)) -> helper (len+1) next
      | Var (_,_) -> len
      in
      let ans = helper 0 root in
(*      Format.printf "check_scrutinee: length `%s` = %d\n%!" (Matchable.show_logic root) ans;*)
      ans
    in
    let count_constructors : IR.logic -> int = fun root ->
      let rec helper seen = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (tag_log,scru,then_,else_)) ->
          let () =
            if check_scrutinee scru > 2 then raise FilteredOut
          in
          let seen_new =
            match (tag_log,Matchable.to_ground scru) with
            | (Value s, Some mat_ground) ->
                if Matchable.height_ground mat_ground > 2 then raise FilteredOut;
                let candidate = (s,mat_ground) in
                if List.mem candidate seen
                then raise FilteredOut
                else
(*                  let () = printf "Adding candidate (%s,%s)\n%!" s (Matchable.show mat_ground) in*)
                  candidate::seen
            | _ -> seen
          in
          let a = helper seen_new then_ in
          let b = helper seen_new else_ in
          (1+a+b)
      in
      helper [] root
    in

  let height_hack ans =
    let max_ifs_count = 6 in (* TODO: populated for simple example *)
    let do_debug = false in

    let prev = ref (Obj.magic false) in
    structural ans IR.reify (fun ir ->
      let verbose = not (!prev = ir) in
      prev := ir;
(*      Format.printf "verbose = %b\n%!" verbose;*)
      let debug fmt =
        Format.ksprintf (fun s -> if do_debug&&verbose then Format.printf "%s" s else ())
          fmt
      in
      try
        debug "height_hack `%s` = %!" (IR.show_logic ir);
        let n = count_constructors ir in
        debug "%d%!" n;
        match n with
        | x when x > max_ifs_count -> raise FilteredOut
        | _ ->
            debug "\n%!";
            true
      with FilteredOut ->
        debug " FILTERED OUT\n%!";
        false
    )
  in


    let hack ideal goal =
      (height_hack ideal) &&&
      goal
    in
(*
    let costf : IR.logic -> OCanren.cost = fun root ->
      let rec helper (low,var) = function
      | Var (_,_)     -> (low,true)
      | Value (Int _)
      | Value (Fail)  -> (0,false)
      | Value (IFTag (_,_,then_,else_)) ->
          let (lw,lf) = helper (0,false) then_ in
          let (rw,rf) = helper (0,false) else_ in
          (lw+rw+1, lf || rf)
      in
      let (n,has_var) = helper (0,false) root in
      let n = if n < 3 then 3 else n in
      if has_var
      then OCanren.CAtLeast n
      else OCanren.CFixed n
    in*)


    let rec list_nth_nat idx xs ans =
      conde
        [ fresh (prev h tl)
            (Nat.one === idx)
            (xs === Std.(h % (ans % tl)))
        ; fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ]
    in

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

    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->
      (*
        Format.printf "structural of '%s' with cname=%a and scru = %s\n"
          (IR.show_logic ir)
          (GT.fmt GT.string) cname
          (Matchable.show scru);
          *)
        let rec helper ir =
          match ir with
          | Var (_,_) -> true
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              let matchable_ground = Matchable.to_ground m in
              if (matchable_ground = Some scru)
              then false
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

    let make_constraint var scru tag =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->

(*        Format.printf "structural of '%s' with cname=%a and scru = %s\n"
          (IR.show_logic ir)
          (GT.fmt GT.string) tag
          (Matchable.show scru);*)

        let fail = false in
        let ok = true in
        let rec helper ir =
          match ir with
          | Var (_,_) -> ok
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru) && (_c = tag)
              then fail
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s ir ans =

        let make_constraints_goal tag ~th ~el scru2 =
          let open Matchable in
          let wrap tag_str scur_g =
             (make_constraint th scur_g tag_str) &&&
             (make_constraint el scur_g tag_str)
          in
          conde
            [ (scru2 === scru   ()) &&& failure
            ; (scru2 === field0 ())
              &&& (conde
                    [ tag === !!"nil"  &&& (wrap "nil"  (Field (Z,Scru)) )
                    ; tag === !!"nil2" &&& (wrap "nil2" (Field (Z,Scru)) )
                    ; tag === !!"cons" &&& (wrap "cons" (Field (Z,Scru)) )
                    ])
              (*&&& (make_constraint2 el (Field (Z,Scru)) )
              &&& (make_constraint2 th (Field (Z,Scru)) )*)

            ; (scru2 === field1 ())
              &&& (conde
                    [ tag === !!"nil"  &&& (wrap "nil"  (Field (S Z,Scru)) )
                    ; tag === !!"nil2" &&& (wrap "nil2" (Field (S Z,Scru)) )
                    ; tag === !!"cons" &&& (wrap "cons" (Field (S Z,Scru)) )
                    ])
              (*&&& (make_constraint2 el (Field (S Z,Scru)))
              &&& (make_constraint2 th (Field (S Z,Scru)))*)

            ; (scru2 === field00()) &&& failure
            ; (scru2 === field01()) &&& failure
            ; (scru2 === field10()) &&& failure
            ; (scru2 === field11()) &&& failure
            ]
        in

        conde
          [ (ir === (fail ())) &&& (ans === (none ()))
          ; fresh (n)
              (ir === (int n))
              (ans === (some n))

          ; fresh (tag scru2 th el q14 tag2 args q16 q6)
              (ir === (iFTag tag scru2 th el))
              (q14 === (eConstr tag2 args))
              (conde
                [ scru2 === Matchable.field0 ()
                ; scru2 === Matchable.field1 ()
(*                ; scru2 === Matchable.field01 ()
                ; scru2 === Matchable.field11 ()
                ; scru2 === Matchable.field10 ()
                ; scru2 === Matchable.field00 ()*)
(*                ; scru2 === Matchable.field000 ()
                ; scru2 === Matchable.field001 ()
                ; scru2 === Matchable.field010 ()
                ; scru2 === Matchable.field011 ()
                ; scru2 === Matchable.field100 ()
                ; scru2 === Matchable.field101 ()
                ; scru2 === Matchable.field110 ()
                ; scru2 === Matchable.field111 ()*)
                ])

              (my_eval_m s scru2 q14)

(*              (conde [tag === !!"cons"; tag === !!"nil"; tag === !!"nil2" ])*)
              (conde
                 [ (tag2 === tag) &&&
                   (make_constraints_goal ~th ~el tag scru2) &&&
                   (self s th ans)
                 ; (tag2 =/= tag) &&&
                   (make_constraints_goal ~th ~el tag scru2) &&&
                   (self s el ans)
                 ])
          ]
      in
      (fun a b c ->
        hack ideal
        (*
        let rec y f x = f (fun z -> y f  z) x in
        y inner a b c
        *)
        (Tabling.(tabledrec three) inner a b c)
      )
    in

    let injected_pats = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
        let prjl e =
          L.prjc
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
        | L.Nil -> EConstr ("nil", Std.List.Nil)
        | L.Nil2 -> EConstr ("nil2", Std.List.Nil)
        | L.Cons (_,tl) ->
            EConstr ("cons", Std.List.of_list id [EConstr ("int", Std.List.Nil); hack_list tl])
        in
        ListLabels.map demo_exprs ~f:(fun (a,b) ->
          EConstr ("pair", Std.List.of_list id [ hack_list a; hack_list b])
        )
      in
(*      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;*)
(*      print_demos "demo_exprs" demo_exprs;*)
      let () =
        demo_exprs |> List.iter (fun e ->
          Format.printf "%s --> %!" (Expr.show e);
          let open OCanren in
          run one (fun ir ->
              let answer_demo = IR.inject possible_answer in
              let scru_demo = Expr.inject e in
              fresh (n rez)
                (eval_pat scru_demo injected_pats rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (my_eval_ir answer_demo scru_demo answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  Format.printf "%s\n%!"
                    (IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify));
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR 2", (fun ideal_IR ->
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
            (my_eval_ir  ideal_IR scru ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));
    Format.printf "%!\n";
    ()

  let _f _ =
    synth_twonillist ~n:(2)
      two_nil_demo_clauses1

end
*)



(*
module TwoNilList2 = struct

  let inhabit_pair_lists = TwoNilList.inhabit_pair_lists
  let inhabit_int = Helper.inhabit_int

  let possible_answer = TwoNilList.possible_answer

  module L = TwoNilList.L

  exception FilteredOut

  let synth_twonillist2 ?(n=10) clauses =
    let check_scrutinee root =
      let rec helper len = function
      | Value Scru -> len+1
      | Value (Field (_, next)) -> helper (len+1) next
      | Var (_,_) -> len
      in
      let ans = helper 0 root in
  (*      Format.printf "check_scrutinee: length `%s` = %d\n%!" (Matchable.show_logic root) ans;*)
      ans
    in
    let count_constructors : IR.logic -> int = fun root ->
      let rec helper seen = function
      | Var (_,_)     -> 0
      | Value (Int _)
      | Value (Fail)  -> 0
      | Value (IFTag (tag_log,scru,then_,else_)) ->
          let () =
            if check_scrutinee scru > 2 then raise FilteredOut
          in
          let seen_new =
            match (tag_log,Matchable.to_ground scru) with
            | (Value s, Some mat_ground) ->
                if Matchable.height_ground mat_ground > 2 then raise FilteredOut;
                let candidate = (s,mat_ground) in
                if List.mem candidate seen
                then raise FilteredOut
                else
  (*                  let () = printf "Adding candidate (%s,%s)\n%!" s (Matchable.show mat_ground) in*)
                  candidate::seen
            | _ -> seen
          in
          let a = helper seen_new then_ in
          let b = helper seen_new else_ in
          (1+a+b)
      in
      helper [] root
    in

  let height_hack ans =
    let max_ifs_count = 6 in (* TODO: populated for simple example *)
    let do_debug = false in

    let prev = ref (Obj.magic false) in
    structural ans IR.reify (fun ir ->
      let verbose = not (!prev = ir) in
      prev := ir;
      let debug fmt =
        Format.ksprintf (fun s -> if do_debug&&verbose then Format.printf "%s" s else ())
          fmt
      in
      try
        debug "height_hack `%s` = %!" (IR.show_logic ir);
        let n = count_constructors ir in
        debug "%d%!" n;
        match n with
        | x when x > max_ifs_count -> raise FilteredOut
        | _ ->
            debug "\n%!";
            true
      with FilteredOut ->
        debug " FILTERED OUT\n%!";
        false
    )
  in

    let hack ideal goal =
      (height_hack ideal) &&&
      goal
    in

    let rec list_nth_nat idx xs ans =
      conde
        [ fresh (prev h tl)
            (Nat.one === idx)
            (xs === Std.(h % (ans % tl)))
        ; fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ]
    in

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

    let make_constraint2 var scru =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->
        let rec helper ir =
          match ir with
          | Var (_,_) -> true
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              let matchable_ground = Matchable.to_ground m in
              if (matchable_ground = Some scru)
              then false
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

    let make_constraint var scru tag =
      (* we should not see the code which tests scru for this constructor *)
      structural var (IR.reify) (fun ir ->

        let fail = false in
        let ok = true in
        let rec helper ir =
          match ir with
          | Var (_,_) -> ok
          | Value (IFTag (Value _c, m, th_, el_)) -> begin
              if (Matchable.to_ground m = Some scru) && (_c = tag)
              then fail
              else (helper th_) && (helper el_)
          end
          | _ -> true
        in
        helper ir
      )
    in

    let my_eval_ir ideal =
      let open Std in
      let rec inner self s ir ans =

        let make_constraints_goal tag ~th ~el scru2 =
          let open Matchable in
          let wrap tag_str scur_g =
             (make_constraint th scur_g tag_str) &&&
             (make_constraint el scur_g tag_str)
          in
          conde
            [ (scru2 === scru   ()) &&& failure
            ; (scru2 === field0 ())
              &&& (conde
                    [ tag === !!"nil"  &&& (wrap "nil"  (Field (Z,Scru)) )
                    ; tag === !!"nil2" &&& (wrap "nil2" (Field (Z,Scru)) )
                    ; tag === !!"cons" &&& (wrap "cons" (Field (Z,Scru)) )
                    ])
              (*&&& (make_constraint2 el (Field (Z,Scru)) )
              &&& (make_constraint2 th (Field (Z,Scru)) )*)

            ; (scru2 === field1 ())
              &&& (conde
                    [ tag === !!"nil"  &&& (wrap "nil"  (Field (S Z,Scru)) )
                    ; tag === !!"nil2" &&& (wrap "nil2" (Field (S Z,Scru)) )
                    ; tag === !!"cons" &&& (wrap "cons" (Field (S Z,Scru)) )
                    ])
              (*&&& (make_constraint2 el (Field (S Z,Scru)))
              &&& (make_constraint2 th (Field (S Z,Scru)))*)

            ; (scru2 === field00()) &&& failure
            ; (scru2 === field01()) &&& failure
            ; (scru2 === field10()) &&& failure
            ; (scru2 === field11()) &&& failure
            ]
        in

        conde
          [ (ir === (fail ())) &&& (ans === (none ()))
          ; fresh (n)
              (ir === (int n))
              (ans === (some n))

          ; fresh (tag scru2 th el q14 tag2 args q16 q6)
              (ir === (iFTag tag scru2 th el))
              (q14 === (eConstr tag2 args))
              (conde
                [ scru2 === Matchable.field0 ()
                ; scru2 === Matchable.field1 ()
  (*                ; scru2 === Matchable.field01 ()
                ; scru2 === Matchable.field11 ()
                ; scru2 === Matchable.field10 ()
                ; scru2 === Matchable.field00 ()*)
  (*                ; scru2 === Matchable.field000 ()
                ; scru2 === Matchable.field001 ()
                ; scru2 === Matchable.field010 ()
                ; scru2 === Matchable.field011 ()
                ; scru2 === Matchable.field100 ()
                ; scru2 === Matchable.field101 ()
                ; scru2 === Matchable.field110 ()
                ; scru2 === Matchable.field111 ()*)
                ])

              (my_eval_m s scru2 q14)

  (*              (conde [tag === !!"cons"; tag === !!"nil"; tag === !!"nil2" ])*)
              (conde
                 [ (tag2 === tag) &&&
                   (make_constraints_goal ~th ~el tag scru2) &&&
                   (self s th ans)
                 ; (tag2 =/= tag) &&&
                   (make_constraints_goal ~th ~el tag scru2) &&&
                   (self s el ans)
                 ])
          ]
      in
      (fun a b c ->
        hack ideal
        (*
        let rec y f x = f (fun z -> y f  z) x in
        y inner a b c
        *)
        (Tabling.(tabledrec three) inner a b c)
      )
    in

    let injected_pats = Clauses.inject clauses in
    let injected_exprs =
      let demo_exprs =
        let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
        let prjl e =
          L.prjc
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
        | L.Nil -> EConstr ("nil", Std.List.Nil)
        | L.Nil2 -> EConstr ("nil2", Std.List.Nil)
        | L.Cons (_,tl) ->
            EConstr ("cons", Std.List.of_list id [EConstr ("int", Std.List.Nil); hack_list tl])
        in
        ListLabels.map demo_exprs ~f:(fun (a,b) ->
          EConstr ("pair", Std.List.of_list id [ hack_list a; hack_list b])
        )
      in
  (*      Printf.printf "\ndemo expressions:%! %s\n%!" @@ GT.show GT.list Expr.show demo_exprs;*)
  (*      print_demos "demo_exprs" demo_exprs;*)
      let () =
        demo_exprs |> List.iter (fun e ->
          Format.printf "%s --> %!" (Expr.show e);
          let open OCanren in
          run one (fun ir ->
              let answer_demo = IR.inject possible_answer in
              let scru_demo = Expr.inject e in
              fresh (n rez)
                (eval_pat scru_demo injected_pats rez)
                (rez === Std.Option.some ir)
                (ir === IR.int n)
                (my_eval_ir answer_demo scru_demo answer_demo (Std.Option.some n))
            )
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
                  Format.printf "%s\n%!"
                    (IR.show_logic ((OCanren.Stream.hd s)#reify IR.reify));
            )
          )
      in
      List.map Expr.inject demo_exprs
    in

    let injected_exprs = List.rev injected_exprs in

    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR 3", (fun ideal_IR ->
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
            (my_eval_ir  ideal_IR scru ideal_IR      res_ir)
          )
          init
          injected_exprs
      ));
    Format.printf "%!\n";
    ()

  let _f () =
    synth_twonillist2 ~n:(2)
      TwoNilList.two_nil_demo_clauses1


end
*)
