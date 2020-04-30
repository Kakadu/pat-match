open OCanren

module Work = Work_unnested
open Work

let id x = x
let (>>=?) x f = match x with None -> None | Some x -> f x

exception FilteredOut


(* TODO: put this to stdlib *)
let rec inject_ground_list ps =
  (* TODO: tail recursion *)
  let rec helper = function
  | Std.List.Nil -> Std.List.nil ()
  | Std.List.Cons (x, xs) -> Std.List.cons x (helper xs)
  in
  helper ps


module Pattern = struct
  type ('a,'b) t = ('a,'b) Work.gpattern = WildCard | PConstr of 'a * 'b
    [@@deriving gt ~options:{fmt; gmap}]

  type ground = (string, ground Std.List.ground) t
  type logic = (string OCanren.logic, logic Std.List.logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = Work.pConstr
  let wc = Work.wildCard

  let rec height = function
  | WildCard  -> 1
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


(* ************************************************************************** *)
module Expr = struct
  type ('a1, 'a0) t = ('a1, 'a0) Work.gexpr = EConstr of 'a1 * 'a0

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


let pwc = WildCard
let pconstr name xs = PConstr (name, Std.List.of_list id xs)
let pleaf s = pconstr s []
let pnil    = pleaf "nil"
let pnil2   = pleaf "nil2"
let pzero   = pleaf "zero"
let ptrue   = pleaf "true"
let pfalse  = pleaf "false"
let pcons a b = pconstr "cons" [a;b]
let psucc a   = pconstr "succ" [a]
let psome a   = pconstr "some" [a]
let ppair a b : Pattern.ground = pconstr "pair" [a;b]


(* ************************************************************************** *)

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
  let rec prjc onvar env xs = For_gnat.prjc (prjc onvar) onvar env xs


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

  let of_int n =
    let rec helper acc n =
      if n = 0 then acc
      else helper (S acc) (n-1)
    in
    if n < 0 then assert false
    else helper Z n
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
(*
  let field000 () : injected = field (z())    @@ field00 ()
  let field001 () : injected = field (z())    @@ field01 ()
  let field010 () : injected = field (z())    @@ field10 ()
  let field011 () : injected = field (z())    @@ field11 ()
  let field100 () : injected = field (s(z())) @@ field00 ()
  let field101 () : injected = field (s(z())) @@ field01 ()
  let field110 () : injected = field (s(z())) @@ field10 ()
  let field111 () : injected = field (s(z())) @@ field11 ()*)

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

  let low_height_of_logic root =
    let rec helper len = function
    | Value (Field (_, next)) -> helper (len+1) next
    | Value Scru
    | Var (_,_) -> len+1
    in
    let ans = helper 0 root in
    (*      Format.printf "check_scrutinee: length `%s` = %d\n%!" (Matchable.show_logic root) ans;*)
    ans
end



(* ************************************************************************** *)


module IR = struct
  type nonrec ('a3, 'a2, 'a1, 'a0) t = ('a3, 'a2, 'a1, 'a0) Work.gir  =
  | Fail
  | IFTag of 'a3 * 'a2 * 'a1 * 'a1
  | Int of 'a0

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
(*    | _ -> failwith "not implemented"*)
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
(*  let show_ocl_small f = function
    | Value x -> f x
    | Var (n,_) -> Printf.sprintf "_.%d" n*)

  let show_ocl_small = show_ocl     (* PRINTING HACK *)

  let rec show_logic e =
    let rec helper = function
    | Fail -> "(fail)"
    | Int ln -> show_ocl_small (GT.show GT.int) ln
    | IFTag (ltag, m, th_, el_) ->
      Printf.sprintf "(iftag %s %s %s %s)"
        (show_ocl (fun s -> Printf.sprintf "\"%s%s\"" (if String.length s = 3 then " " else "") s) ltag)
        (Matchable.show_logic m)
        (show_logic th_)
        (show_logic el_)
(*    | _ -> Printf.sprintf "<logic ir>"*)
    in
    show_ocl_small helper e


  let count_ifs_ground root =
    let rec helper acc = function
    | Fail -> acc
    | Int _ -> acc
    | IFTag (_,_,th,el) ->
        helper (helper (1+acc) th) el
    in
    helper 0 root

  let count_ifs_low : logic -> int = fun root ->
    let rec helper = function
    | Var (_,_)     -> 0
    | Value (Int _)
    | Value (Fail)  -> 0
    | Value (IFTag (tag_log,scru,then_,else_)) ->
        let a = helper then_ in
        let b = helper else_ in
        (1+a+b)
    in
    helper root


end


module Clauses = struct
  type pg = Pattern.ground * IR.ground
  type pre_ground = pg list
  type ground = pg Std.List.ground
  type logic = (Pattern.logic, IR.logic) Std.Pair.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected

  let inject : pre_ground -> injected = fun ps ->
    let rec one : Pattern.ground -> _ = function
    | WildCard -> Pattern.wc ()
    | PConstr (name,ps) ->
        Pattern.constr !!name @@
        (inject_ground_list @@ GT.gmap Std.List.ground one ps)
    in

    Std.List.list @@
    List.map (fun (p,rhs) -> Std.Pair.pair (one p) (IR.inject rhs)) ps


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
