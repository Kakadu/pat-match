module Work = Work_unnested
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

(*type name = string
let name =
  { GT.gcata = ()
  ; fix = ()
  ; plugins = object
      method fmt f = Format.fprintf f "%s"
  end }*)

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

let _ =
  run_exn (Format.asprintf "%a" (pp_maybe pp_rhs)) 1 q qh ("answers", fun q ->
    checkAnswer (pair (leaf "aaa") (leaf "bbb"))
      (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
      q
  )

let _ =
  runR Expr.reify Expr.show Expr.show_logic
        1 q qh ("answers", fun q ->
     checkAnswer
        q
        (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
        (Std.some (!!2))
  )

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
    | Scru          -> "Scru"
    | Field (n,r) ->
      Printf.sprintf "(field %s %s)" (Nat.show_logic n) (show_logic r)
    in
    GT.show OCanren.logic helper x

  let show x =
    let rec helper = function
    | Scru        -> "Scru"
    | Field (n,r) -> Printf.sprintf "(field %s %s)" (Nat.show n) (helper r)
    in
    helper x

end


module IR = struct
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
    | _ -> failwith "not implemented"
    in
    helper e

  let show e =
    let rec helper = function
    | Fail -> "(fail)"
    | Int n -> string_of_int n
    | IFTag (str, m, th_, el_) ->
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

(*  let show_ocl_small = show_ocl     (* PRINTING HACK *)*)

  let rec show_logic e =
    let rec helper = function
    | Fail -> "(fail)"
    | Int ln -> show_ocl_small (GT.show GT.int) ln
    | IFTag (ltag, m, th_, el_) ->
      Printf.sprintf "(iftag %s %s %s %s)"
        (show_ocl_small (fun s -> sprintf "\"%s%s\"" (if String.length s = 3 then " " else "") s) ltag)
        (Matchable.show_logic m)
        (show_logic th_)
        (show_logic el_)
(*    | _ -> Printf.sprintf "<logic ir>"*)
    in
    show_ocl_small helper e
end


module Clauses = struct
  type ground = (Pattern.ground * IR.ground) Std.List.ground
  type logic = (Pattern.logic, IR.logic) Std.Pair.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected
end


let inject_patterns ps =
  let rec one : Pattern.ground -> _ = function
  | WildCard -> Pattern.wc ()
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

  let run_hacky ?(n=10) patterns2 =
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
          run one (fun ir -> eval_pat (Expr.inject e) injected_pats (Std.Option.some ir))
            (fun r -> r)
            |> (fun s ->
                  assert (not (OCanren.Stream.is_empty s));
(*                  let (_:int)  = (OCanren.Stream.hd s) in*)
                  print_endline @@ IR.show_logic  ((OCanren.Stream.hd s)#reify IR.reify);
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
      | Value (IFTag (_,_,then_,else_)) ->
          let a = helper then_ in
          let b = helper else_ in
          (1+a+b)
      in
      helper root
    in

    let flip f a b = f b a in

    let height_hack ans =
      fortytwo ans (flip IR.reify) (fun ir ->
        let n = count_constructors ir in
(*        Format.printf "%d == min height of `%s`\n%!" n (IR.show_logic ir);*)
        match count_constructors ir with
        | x when x>3 -> failure
        | _ -> success
      )
    in

(*
    (* Not fast enough *)
    let rec my_eval_ir s ir ans =
      let open Std in
      conde
        [ (ir === (fail ())) &&& (ans === (none ()))
        ; fresh (n)
            (ir === (int n))
            (ans === (some n))
        ; fresh (tag scru2 th el q14 tag2 args q16)
            (ir === (iFTag tag scru2 th el))
            (q14 === (eConstr tag2 args))
            (eval_m s scru2 q14)

            (conde [tag === !!"nil"; tag === !!"cons"; tag === !!"pair"])
            (let open Matchable in
             conde
              [ (scru2 === scru   ()) &&& (tag === !!"pair")
              ; (scru2 === field0 ()) &&& (conde [tag === !!"nil"; tag === !!"cons"])
              ; (scru2 === field1 ()) &&& (conde [tag === !!"nil"; tag === !!"cons"])
              ; (scru2 === field00()) &&& failure
              ; (scru2 === field01()) &&& failure
              ; (scru2 === field10()) &&& failure
              ; (scru2 === field11()) &&& failure
              ])

            (conde
               [ (tag2 === tag) &&& (q16 === !!true)
               ; (q16 === !!false) &&& (tag2 =/= tag)
               ])
            (conde
               [ (q16 === !!true)  &&& (my_eval_ir s th ans)
                    &&& (height_hack th)
               ; (q16 === !!false) &&& (my_eval_ir s el ans)
                    &&& (height_hack el)
               ])
        ]
    in
*)

(*
    let rec list_nth_nat idx xs ans =0
      conde
        [ fresh (x q63)
            (Nat.z === idx)
            (xs === Std.(ans % q63))
        ; fresh (prev h tl)
            ((Nat.s prev) === idx)
            (xs === Std.(h % tl))
            (list_nth_nat prev tl ans)
        ]
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
                  (*(tag === !!"pair") &&& (el === fail())*)
              ; (conde [ scru2 === field0 (); scru2 === field1 () ])
                &&&
                (conde [ tag === !!"nil"
(*                            &&& (fresh (u v) (el =/= (iFTag !!"cons" scru2 u v)))
                            &&& (fresh (u v) (el =/= (iFTag !!"nil"  scru2 u v)))*)
                       ; tag === !!"cons"
                            (*&&& (fresh (u v) (el =/= (iFTag !!"cons" scru2 u v)))
                            &&& (fresh (u v) (el =/= (iFTag !!"nil"  scru2 u v)))*)
                       ])

              ; (scru2 === field00()) &&& failure
              ; (scru2 === field01()) &&& failure
              ; (scru2 === field10()) &&& failure
              ; (scru2 === field11()) &&& failure
              ])


          (* next two variants seems to be equivalent *)
(*
            (conde
               [ (tag2 === tag) &&& (self s th ans)
               ; (tag2 =/= tag) &&& (self s el ans)
               ])
               *)
           (conde
              [(tag2 === tag) &&& (q6 === (!! true));
              (q6 === (!! false)) &&& (tag2 =/= tag)])
           (conde
              [(q6 === (!! true)) &&& (self s th ans);
              (q6 === (!! false)) &&& (self s el ans)])

           (* Commenting next line leads to no answers *)
           (height_hack ideal)
        ]
      in
(*      inner  s ir ans*)
      Tabling.(tabledrec three) inner
    in

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
            (my_eval_ir  ideal_IR scru ideal_IR      res_ir)
          )
          init
          injected_exprs
      );

    Format.printf "%!\n";


    runR IR.reify IR.show IR.show_logic n
      q qh ("ideal_IR hinted", fun ideal_IR ->
        let init =
          fresh (th el)
            (IR.iftag !!"nil" Matchable.(field (s(z())) (scru())) th el === ideal_IR)
        in
        List.fold_left (fun acc (scru: Expr.injected) ->
          fresh (res_pat res_ir)
            acc
            (eval_pat             scru injected_pats res_pat)
            (my_eval_ir  ideal_IR scru ideal_IR      res_ir)
            (conde
              [ fresh (n)
                 (res_pat === Std.Option.some (IR.int n))
                 (res_ir  === Std.Option.some n)
              ; (res_pat === Std.Option.none ()) &&& (res_ir === Std.Option.none())
              ])
          ) init injected_exprs
      )

  let () =
    run_hacky ~n:60
      [ ppair pnil  pwc, IR.eint 10
      ; ppair pwc  pnil, IR.eint 20
      ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 30
      ]

end
