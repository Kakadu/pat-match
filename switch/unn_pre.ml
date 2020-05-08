open OCanren

open Work

let id x = x
let (>>=?) x f = match x with None -> None | Some x -> f x
let failwiths fmt = Printf.ksprintf failwith fmt

let simple_shortcut _ _ _ ans = (ans === !!true)

exception FilteredOut

(* ************************************************************************** *)
module Nat = struct
  type 'a gnat = 'a Work.gnat = Z | S of 'a [@@deriving gt ~options:{fmt; foldl; gmap}]
  type ground = ground gnat
    [@@deriving gt ~options:{fmt; foldl; gmap}]
  type logic = logic gnat OCanren.logic
    [@@deriving gt ~options:{fmt; foldl; gmap}]
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

(* ************************************************************************** *)
let string_of_tag_exn = function
| 0 -> "zero"
| 1 -> "succ"
| 2 -> "true"
| 3 -> "false"
| 5 -> "nil"
| 6 -> "cons"
| 7 -> "nil2"
| 9 -> "pair"
| 10 -> "A"
| 11 -> "B"
| 12 -> "C"
| 13 -> "int"
| 14 -> "triple"
| n -> failwith (Printf.sprintf "Bad argument %d in tag_of_string_exn" n)

let tag_of_string_exn = function
| "zero" -> 0
| "succ" -> 1
| "true" -> 2
| "false" -> 3
| "nil" -> 5
| "cons" -> 6
| "nil2" -> 7
| "pair" -> 9
| "A"    -> 10
| "B"    -> 11
| "C"    -> 12
| "int"  -> 13
| "triple" -> 14
| s -> failwith (Printf.sprintf "Bad argument %S in tag_of_string_exn" s)

type tag = GT.int
  [@@deriving gt]

let tag =
  { GT.gcata = gcata_tag
  ; GT.fix = tag.GT.fix
  ; GT.plugins = object
      method show = string_of_tag_exn
      method fmt f x = Format.fprintf f "%s" (string_of_tag_exn x)
      method gmap x = x
  end}

type tagl = GT.int OCanren.logic
  [@@deriving gt]

let tagl =
  { GT.gcata = gcata_tagl
  ; GT.fix = tagl.GT.fix
  ; GT.plugins = object
      method show = GT.show OCanren.logic string_of_tag_exn
      method fmt f l = GT.fmt OCanren.logic (fun fmt x -> Format.fprintf fmt "%s" (string_of_tag_exn x)) f l
      method gmap x = x
  end}


(* TODO: put this to stdlib *)
let rec inject_ground_list (xs : ('a, 'b) OCanren.injected Std.List.ground) : ('a, 'b) Std.List.groundi =
  (* TODO: tail recursion *)
  let rec helper = function
  | Std.List.Nil -> Std.List.nil ()
  | Std.List.Cons (x, xs) -> Std.List.cons x (helper xs)
  in
  helper xs

let ground_list_length xs =
  GT.foldl Std.List.ground (fun acc _ -> acc+1) 0 xs


let logic_list_len_lo =
  let rec helper acc = function
    | Var (_,_) -> acc
    | Value (Std.List.Cons (_, tl)) -> helper (acc+1) tl
    | Value Std.List.Nil -> acc
  in
  helper 0

module Pattern = struct
  type ('a,'b) t = ('a,'b) Work.gpattern =
    | WildCard
    | PConstr of 'a * 'b
    [@@deriving gt ~options:{fmt; gmap}]

  type ground = (tag, ground Std.List.ground) t
  type logic = (tag OCanren.logic, logic Std.List.logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = Work.pConstr
  let wc = Work.wildCard

  let rec height = function
  | WildCard  -> 1
  | PConstr (_,ps) ->
    GT.foldl Std.List.ground (fun acc x -> max acc (height x)) 0 ps + 1

  let show : ground -> string =
    let rec helper = function
    | WildCard -> "_"
    | PConstr (s, Std.List.Nil) -> Printf.sprintf "(%s)" (GT.show tag s)
    | PConstr (s, ps) ->
      Printf.sprintf "(%s %s)" (GT.show tag s) (GT.show Std.List.ground helper ps)
    in
    helper

  let rec show_logic (p: logic) =
    let rec helper = function
    | WildCard -> "_"
    | PConstr (s, OCanren.Value Std.List.Nil) ->
        GT.show OCanren.logic (GT.show tag) s
    | PConstr (s, ps) ->
      Printf.sprintf "(%s %s)"
        (match s with
          | OCanren.Value s -> GT.show tag s
          | s -> GT.show OCanren.logic (GT.show tag) s)
        (GT.show Std.List.logic show_logic ps)
    in
    GT.show OCanren.logic helper p


  module ArityMap = Map.Make(Base.Int)
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

  type ground = (tag, ground Std.List.ground) gexpr
  type logic  = (tag OCanren.logic, logic Std.List.logic) gexpr OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = eConstr
  let econstr s xs = EConstr (tag_of_string_exn s, Std.List.of_list id xs)

  let show : ground -> string   =
    let rec helper pars x =
     match x with
    | EConstr (c, Std.List.Nil) when pars -> Printf.sprintf "(%s)" (GT.show tag c)
    | EConstr (c, Std.List.Nil)           -> GT.show tag c
    | EConstr (s, xs) when pars ->
      Printf.sprintf "(%s %s)"
        (GT.show tag s)
        (GT.show Std.List.ground (helper false) xs)
    | EConstr (s, xs) ->
      Printf.sprintf "%s %s"
        (GT.show tag s)
        (GT.show Std.List.ground (helper false) xs)
    in
    helper false

  let rec show_logic (x: logic) : string =
    let rec helper x =
      match x with
      | EConstr (s, xs) ->
        Printf.sprintf "(%s %s)"
          (GT.show OCanren.logic (GT.show tag) s)
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
let pleaf s = pconstr (tag_of_string_exn s) []
let pnil    = pleaf "nil"
let pnil2   = pleaf "nil2"
let pzero   = pleaf "zero"
let ptrue   = pleaf "true"
let pfalse  = pleaf "false"
let pcons a b = pconstr (tag_of_string_exn "cons") [a;b]
let psucc a   = pconstr (tag_of_string_exn "succ") [a]
let psome a   = pconstr (tag_of_string_exn "some") [a]
let ppair a b = pconstr (tag_of_string_exn "pair") [a;b]
let ptriple a b c = pconstr (tag_of_string_exn "triple") [a;b;c]

(* ************************************************************************** *)

module Matchable = struct
  type ('a1, 'a0) gmatchable = ('a1, 'a0) Work.gmatchable =
    | Scru
    | Field of 'a1 * 'a0
    [@@deriving gt ~options:{ foldl; fmt; gmap }]
  type ground = (Nat.ground, ground) gmatchable
    [@@deriving gt ~options:{ foldl; fmt; gmap }]
  type logic = (Nat.logic, logic) gmatchable OCanren.logic
    [@@deriving gt ~options:{ foldl; fmt; gmap }]
  type injected = (ground, logic) OCanren.injected

  let scru = scru
  let field = field

  let field0  () = field (z())    @@ scru()
  let field1  () = field (s(z())) @@ scru()
  let field00 () = field (z())    @@ field0 ()
  let field01 () = field (s(z())) @@ field0 ()
  let field10 () = field (z())    @@ field1 ()
  let field11  () : injected = field (s(z())) @@ field1 ()

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

  let ground =
    { GT.gcata = gcata_ground
    ; GT.fix = ground.GT.fix
    ; GT.plugins = object
        method fmt f x = Format.fprintf f "%s" (show x)
        method show = show
        method gmap = ground.GT.plugins#gmap
      end
    }
  let logic =
    { GT.gcata = gcata_logic
    ; GT.fix = logic.GT.fix
    ; GT.plugins = object
        method fmt f x = Format.fprintf f "%s" (show_logic x)
        method show = show_logic
        method gmap = logic.GT.plugins#gmap
      end
    }


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
  | Switch of 'a3 * 'a2 * 'a1
  | Lit of 'a0
  [@@deriving gt ~options: { show; fmt; gmap} ]

  type ground = (Matchable.ground, (tag, ground) Std.Pair.ground Std.List.ground, ground, GT.int) t
    [@@deriving gt ~options: { show; fmt; gmap } ]
  type logic = (Matchable.logic, (tag OCanren.logic, logic) Std.Pair.logic Std.List.logic, logic, GT.int OCanren.logic) t OCanren.logic
    [@@deriving gt ~options: { show; fmt; gmap} ]
  type injected = (ground, logic) OCanren.injected

  let fail = fail
  let switch = switch
  let int = lit
  let lit = lit

  let eint n = Lit n

  let rec reify env =
    For_gir.reify Matchable.reify (Std.List.reify @@ Std.Pair.reify OCanren.reify reify)
      reify OCanren.reify env

  let fmt f (ir: ground) =
    GT.transform ground
      (fun fself -> object
        inherit [_] fmt_ground_t fself
        method! c_Fail fmt _ = Format.fprintf fmt "fail"
        method! c_Lit fmt _ n = Format.fprintf fmt "%d" n
        method! c_Switch fmt _ m xs on_default =
          Format.fprintf fmt "@[(@[match@ %a@ with@]@ " (GT.fmt Matchable.ground) m;
          GT.foldl Std.List.ground (fun () (t, code) ->
            Format.fprintf fmt "@[| %a ->@ %a @]"
              (GT.fmt tag) t
              fself code
          ) () xs;
          Format.fprintf fmt "@[| _ ->@ %a@]" fself on_default;
          Format.fprintf fmt ")@]"
      end)
      f
      ir

  let show e =
    let (_:string) = Format.flush_str_formatter () in
    Format.pp_set_margin Format.str_formatter 10000;
    Format.pp_set_max_indent Format.str_formatter (Format.pp_get_margin Format.std_formatter () - 1);
    Format.fprintf Format.str_formatter "%a" fmt e;
    Format.flush_str_formatter ()

  let show_ocl f = GT.show OCanren.logic f
(*  let show_ocl_small f = function
    | Value x -> f x
    | Var (n,_) -> Printf.sprintf "_.%d" n*)

  let show_ocl_small = show_ocl     (* PRINTING HACK *)

  let rec fmt_logic fmt (e: logic) =
    let fmt_ocl fmt f x = GT.fmt OCanren.logic f fmt x in
    let rec helper fmt = function
      | Fail -> Format.fprintf fmt "fail"
      | Lit ln -> fmt_ocl fmt (GT.fmt GT.int) ln
      | Switch  (m, xs, default) ->
        Format.fprintf fmt "(switch %a with" (GT.fmt Matchable.logic) m;
        GT.foldl Std.List.logic (
          GT.foldl OCanren.logic
            (fun () (tag, irl) ->
              Format.fprintf fmt "@[@ |@ %a@ ->@ %a@]" (GT.fmt tagl) tag fmt_logic irl
            )
        ) () xs;
        Format.fprintf fmt "%a)" fmt_logic default
    in
    fmt_ocl fmt helper e

(*
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
    in
    show_ocl_small helper e*)

  let show_logic e =
    let (_:string) = Format.flush_str_formatter () in
    Format.pp_set_margin Format.str_formatter 10000;
    Format.pp_set_max_indent Format.str_formatter (Format.pp_get_margin Format.std_formatter () - 1);
    Format.fprintf Format.str_formatter "%a" fmt_logic e;
    Format.flush_str_formatter ()

  let ground =
    { GT.gcata = gcata_ground
    ; GT.fix = ground.GT.fix
    ; GT.plugins = object
        method fmt  = fmt
        method show = show
        method gmap = ground.GT.plugins#gmap
      end
    }
  let logic =
    { GT.gcata = gcata_logic
    ; GT.fix = logic.GT.fix
    ; GT.plugins = object
        method fmt  = fmt_logic
        method show = show_logic
        method gmap = logic.GT.plugins#gmap
      end
    }

  let inject: ground -> injected =
    let rec helper = function
    | Lit n -> int !!n
    | Fail -> fail ()
    | Switch (m, xs, default) ->
        let clauses = inject_ground_list @@
          GT.gmap Std.List.ground (fun (tag,code) -> Std.Pair.pair !!tag (helper code)) xs
       in
       switch (Matchable.inject m) clauses (helper default)
    (*| IFTag (str, matchable, th, el) ->
      iftag !!str (Matchable.inject matchable) (helper th) (helper el)*)

    in
    helper


  let count_ifs_ground root =
    GT.transform ground
      (fun fself -> object
        method c_Fail acc _ = acc
        method c_Lit  acc _ _ = acc
        method c_Switch acc _ _ xs on_default =
          GT.foldl Std.List.ground
            (fun acc (_tag, code) -> fself acc code) (fself acc on_default) xs
          + (ground_list_length xs)
      end)
      0
      root

  let count_ifs_low : logic -> int = fun root ->
    let rec helper : logic -> int = function
    | Var (_,_)     -> 0
    | Value (Lit _)
    | Value (Fail)  -> 0
    | Value (Switch (scru, xs, on_default)) ->
              GT.foldl Std.List.logic (fun acc -> function
                | Value (_, code) -> acc + (helper code)
                | Var _ -> acc)
                (logic_list_len_lo xs)
                xs
          +
          (helper on_default)

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


  let pretty_print ch clauses =
    Format.fprintf ch "@[match ... with@]@.";
    clauses |> List.iter (fun (p,ir) ->
      Format.fprintf ch "@[| %s@ ->@ %s@]@." (Pattern.show p) (IR.show ir)
    )

end



module Typs = struct
  type 'a t = 'a Work.gtyp_info = T of 'a
    [@@deriving gt ~options: { show; fmt }]
  type ground = (tag,             ground Std.List.ground) Std.Pair.ground  Std.List.ground t
    [@@deriving gt ~options: { show; fmt }]
  type logic  = (tag OCanren.logic, logic Std.List.logic) Std.Pair.logic   Std.List.logic t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let t eta = Work.t eta
  let t_item name xs = Std.Pair.pair name xs

  let rec inject (e: ground) : injected =
    let rec helper : tag * ground Std.List.ground -> _ = function
    | (s, xs) ->
        t_item !!s (inject_ground_list @@ GT.gmap Std.List.ground inject xs)
    in
    match e with
    | T xs -> t (inject_ground_list @@ GT.gmap Std.List.ground helper xs)

  let mkt xs: ground = T (Std.List.of_list id xs)

  type pre_typ = (string * pre_typ list) list t
  let rec construct (root: pre_typ) : ground =
    match root with
    | T xs -> mkt @@ List.map (fun (p,xs) -> (tag_of_string_exn p, Std.List.of_list construct xs)) xs
end


module Triple = struct
  type ('a,'b,'c) ground = 'a * 'b * 'c [@@deriving gt ~options:{fmt;gmap}]
  module F = Fmap3(struct
      type ('a,'b,'c) t = ('a,'b,'c) ground
      let fmap eta = GT.gmap ground eta
    end)

  type nonrec ('a,'b,'c) logic = ('a,'b,'c) ground OCanren.logic

  let reify fa fb fc = F.reify fa fb fc
  let prjc = F.prjc
  let make x y z = inj @@ F.distrib (x,y,z)
end
