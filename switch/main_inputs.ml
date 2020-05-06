open Unn_pre


module type ARG0 = sig
  open OCanren

  type g
  type l
  type qtyp_injected = (g,l) injected


  val inhabit: int -> qtyp_injected -> goal
  val clauses : Clauses.pre_ground
  val typs : Typs.injected
  val max_height : int
  val optimize: IR.ground -> IR.ground
  val prjp: OCanren.Env.t -> qtyp_injected -> g
  val wrap_demo: g list -> Expr.ground list

  val shortcut:
    (tag, tag logic) injected -> Matchable.injected ->
    (bool, bool logic) injected -> goal

  val info : string
end

module type ARG1 = sig
  include ARG0
  val possible_answer: IR.ground
  (* maximum count of IFs in the example answer *)
  val max_ifs_count : int

  val ir_hint : IR.injected -> OCanren.goal
end

(* ************************************************************************** *)
module ArgTrueFalse : ARG0 = struct
  open OCanren

  type g = bool
  type l = bool logic
  type qtyp_injected = (g, l) OCanren.injected

  let inhabit_pair :
      Std.Nat.groundi ->
      qtyp_injected ->
      goal
    = fun height rez ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev l r)
          (Std.Nat.succ prev === height)
          (conde
            [ (rez === !!true)
            ; (rez === !!false)
            ])
      ]

  let inhabit n rez = inhabit_pair (Std.nat n) rez

  let info = "bool"

  let clauses =
    [ ptrue, IR.eint 1
    ; pfalse, IR.eint 0
    ]

  let max_height =
    let n = Helper.List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
  (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (1 = n);
    n

  let typs =
    let open Unn_pre.Typs in

    let grounded = Typs.construct @@ T [ ("true", []); ("false", []) ]  in
    Typs.inject grounded

  let rec optimize (root: IR.ground)  = root

  let prjp e =
    OCanren.prjc
      (fun _ _ -> failwith "should not happen5")
      e

  let wrap_demo (demo_exprs: bool list) =
    let open Unn_pre.Expr in
    let rec helper = function
    | true  -> econstr "true" []
    | false -> econstr "false" []
    in
    ListLabels.map demo_exprs ~f:helper

  let shortcut = simple_shortcut
end


(* ************************************************************************** *)
module ArgABC : ARG0 = struct
  open OCanren

  type abc = A | B | C
  type g = abc
  type l = abc  logic
  type qtyp_injected = (g, l) OCanren.injected

  let inhabit_pair :
      Std.Nat.groundi ->
      qtyp_injected ->
      goal
    = fun height rez ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev l r)
          (Std.Nat.succ prev === height)
          (conde
            [ (rez === !!A)
            ; (rez === !!B)
            ; (rez === !!C)
            ])
      ]

  let inhabit n rez = inhabit_pair (Std.nat n) rez

  let info = "A|B|C"

  let clauses =
    [ pleaf "A", IR.eint 1
    ; pleaf "B", IR.eint 1
    ; pleaf "C", IR.eint 0
    ]

  let max_height =
    let n = Helper.List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
  (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (1 = n);
    n

  let typs =
    let open Unn_pre.Typs in

    let grounded = Typs.construct @@ T [ ("A", []); ("B", []); ("C", []) ] in
    Typs.inject grounded

  let rec optimize (root: IR.ground)  = root

  let prjp e =
    OCanren.prjc
      (fun _ _ -> failwith "should not happen5")
      e

  let wrap_demo (demo_exprs: g list) =
    let open Unn_pre.Expr in
    let rec helper = function
    | A  -> econstr "A" []
    | B  -> econstr "B" []
    | C  -> econstr "C" []
    in
    ListLabels.map demo_exprs ~f:helper

  let shortcut = simple_shortcut
end


let optimize_pair: IR.ground -> IR.ground =
  let open OCanren  in
  let open Unn_pre.IR in
  let open Unn_pre.Matchable in


  GT.transform IR.ground
    (fun fself -> object
      inherit [_,_] IR.gmap_ground_t fself
      method! c_Switch acc me _m xs default =
        match xs with
        | Std.List.Nil -> fself () default
        | Std.List.Cons ( (t, then_), Std.List.Nil) when string_of_tag_exn t = "pair" -> fself () then_
        | _ -> fself () me
    end)
    ()


(* ************************************************************************** *)
module ArgPairTrueFalse : ARG0 (*with type g = bool * bool
                               and  type l = (bool OCanren.logic, bool OCanren.logic) OCanren.Std.Pair.logic
                               and qtyp_injected = (g, l) OCanren.injected
                               *)
                 = struct
  open OCanren

  type g = bool * bool
  type l = (bool logic, bool logic) Std.Pair.logic
  type qtyp_injected = (g, l) OCanren.injected

  let inhabit_bool :
      Std.Nat.groundi ->
      (bool, bool logic) injected  ->
      goal
    = fun height rez ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev l r)
          (Std.Nat.succ prev === height)
          (conde
            [ (rez === !!true)
            ; (rez === !!false)
            ])
      ]

  let inhabit_pair :
      Std.Nat.groundi ->
      qtyp_injected ->
      goal
    = fun height rez ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev l r)
          (Std.Nat.succ prev === height)
          (rez === Std.pair l r)
          (inhabit_bool prev l)
          (inhabit_bool prev r)
      ]

  let inhabit n rez = inhabit_pair (Std.nat n) rez

  let info = "bool*bool"

  let clauses =
    [ ppair ptrue pwc , IR.eint 1
    ; ppair pwc ptrue , IR.eint 1
    ; ppair pfalse pfalse, IR.eint 0
    ]

  let max_height =
    let n = Helper.List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
  (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (2 = n);
    n

  let optimize = optimize_pair

  let typs =
    let open Unn_pre.Typs in

    let bool = T [ ("true", []); ("false", []) ]  in
    let p    = T [ ("pair", [bool; bool]) ] in
    Typs.inject @@ Typs.construct p

  let prjp e =
    let prjl e =
      OCanren.prjc
        (fun _ _ -> failwith "should not happen2")
        e
      in
      Std.Pair.prjc prjl prjl
        (fun _ _ -> failwith "should not happen5")
        e


  let wrap_demo (demo_exprs: g list) =
    let open Unn_pre.Expr in
    let rec helper = function
    | true  -> econstr "true" []
    | false -> econstr "false" []
    in
    ListLabels.map demo_exprs ~f:(fun (a,b) ->
      econstr "pair" [ helper a; helper b]
    )

  let shortcut = simple_shortcut

end

(* ************************************************************************** *)
module ArgPeanoSimple : ARG0 = struct
  open OCanren

  type g = (Nat.ground, Nat.ground) OCanren.Std.Pair.ground
  type l = (Nat.logic, Nat.logic) OCanren.Std.Pair.logic
  type qtyp_injected = (g, l) OCanren.injected

  let rec inhabit_nat :
      Std.Nat.groundi ->
      Nat.injected ->
      goal
    = fun height r ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev)
          (Std.Nat.succ prev === height)
          (conde
            [ (r === Nat.z)
            ; fresh (size_tl tl)
                (Nat.s tl === r)
                (inhabit_nat prev tl)
            ])
      ]

  let inhabit_pair :
      Std.Nat.groundi ->
      qtyp_injected ->
      goal
    = fun height rez ->
    conde
      [ (Std.Nat.zero === height) &&& failure
      ; fresh (prev l r)
          (Std.Nat.succ prev === height)
          (rez === Std.pair l r)
          (inhabit_nat prev l)
          (inhabit_nat prev r)
      ]

  let inhabit n rez = inhabit_pair (Std.nat n) rez

  let info = "simple nats (a la Maranget2008)"

  let clauses =
    [ ppair (psucc pwc) (psucc pwc), IR.eint 30
    ; ppair pzero  pwc, IR.eint 10
    ; ppair pwc  pzero, IR.eint 10
    ;
    ]

  let max_height =
    let n = Helper.List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
  (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (3 = n);
    n


  let typs =
    let open Unn_pre.Typs in

    let make prev =
      T [ ("zero", [])
        ; ("succ", [ prev ])
        ]
    in
    let empty = T [ ("zero", []);  ] in
    let height1 = make empty in
    let height2 = make height1 in
    let height3 = make height2 in
    let pairs = T [ ("pair", [ height3; height3 ]) ] in
    let grounded = Typs.construct pairs in
    Typs.inject grounded

  let optimize = optimize_pair

  let prjp e =
    let prjl e =
      Nat.prjc
        (fun _ _ -> failwith "should not happen2")
        e
      in
    Std.Pair.prjc prjl prjl
      (fun _ _ -> failwith "should not happen5")
      e

  let wrap_demo (demo_exprs: (Nat.ground * Nat.ground) list) =
    let open Unn_pre.Expr in
    let rec helper = function
    | Nat.Z -> econstr "zero" []
    | Nat.S tl ->
        econstr "succ" [ helper tl ]
    in
    ListLabels.map demo_exprs ~f:(fun (a,b) ->
      econstr "pair" [ helper a; helper b ]
    )

  let shortcut = simple_shortcut
end

module ArgSimpleList : ARG0 = struct
  open OCanren

  type g = (int Std.List.ground, int Std.List.ground) Std.Pair.ground
  type l = (int logic Std.List.logic, int logic Std.List.logic) Std.Pair.logic
  type qtyp_injected = (g, l) injected

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
    run one (inhabit_list (Std.nat 2) Helper.inhabit_free)
      (fun r -> r#reify (Std.List.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt Std.List.logic @@ (fmt OCanren.logic @@ fmt bool)) x
       )
    |> OCanren.Stream.take ~n:(10) |> ignore;
    Format.printf "\n%!"

  let _comment () =
    run one (inhabit_list (Std.nat 1) Helper.inhabit_free)
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

  let inhabit n rez = inhabit_pair_lists (Std.nat n) Helper.inhabit_int rez

  let info = "simple lists (from Maranget2008)"

  let clauses =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 20
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 30
    ]

  let max_height =
    let n = Helper.List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
  (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (3 = n);
    n

  let typs =
    let open Unn_pre.Typs in
    let ints = T [ ("int",[]) ] in
    let list_empty = T [  ("nil", []);  ] in
    let listints1 = T [ ("nil", []);  ("cons", [ ints; list_empty]) ] in
    let listints2 = T [ ("nil", []);  ("cons", [ ints; listints1]) ] in
    let pairs = T [ ("pair", [ listints2; listints2]) ] in
    let grounded = Typs.construct pairs in
    Typs.inject grounded


  let optimize = optimize_pair

  module L = OCanren.Std.List

  let prjp e =
    let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
    let prjl e =
      L.prjc
        prj1
        (fun _ _ -> failwith "should not happen2")
        e
      in
    Std.Pair.prjc prjl prjl
      (fun _ _ -> failwith "should not happen5")
      e

  let wrap_demo demo_exprs =
    let open Unn_pre.Expr in
    let rec hack_list = function
    | L.Nil -> econstr "nil" []
    | L.Cons (_,tl) ->
        econstr "cons"  [ econstr "int" []; hack_list tl ]
    in
    ListLabels.map demo_exprs ~f:(fun (a,b) ->
      econstr "pair" [ hack_list a; hack_list b ]
    )

  let shortcut = simple_shortcut
end



module TwoNilList = struct
  open Helper
  open OCanren

  module L = struct
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


end

(* ************************************************************************** *)
module ArgTwoNilLists1 : ARG0 = struct
  open OCanren

  type g = (int TwoNilList.L.ground, int TwoNilList.L.ground) OCanren.Std.Pair.ground
  type l = (int OCanren.logic TwoNilList.L.logic, int OCanren.logic TwoNilList.L.logic) OCanren.Std.Pair.logic
  type qtyp_injected = (g, l) OCanren.injected

  let inhabit n rez = TwoNilList.inhabit_pair_lists (Std.nat n) Helper.inhabit_int rez

  let info = "two-nil lists (no cons -- use WCs)"

  let clauses =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 20
    ; ppair pnil2 pwc, IR.eint 30
    ; ppair pwc pnil2, IR.eint 40
    ; ppair pwc pwc, IR.eint 60
    ]

  let max_height =
    (* although maximum height is 2 we can construct right examples yet *)
    (* TODO: understand how to fix this *)
    (*
    let n = Helper.List.max (List.map (fun (p,_) -> Pattern.height p) clauses) in
    Format.printf "patterns max height = %d\n%!" n;
    assert (3 = n);
    n
    *)
    3


  let typs =
    let open Unn_pre in
    let open Unn_pre.Typs in
    let ints = T [ ("int",[]) ] in
    let list_empty = T [ ("nil", []); ("nil2", []) ] in
    let listints1  = T [ ("nil", []); ("nil2", []); ("cons", [ ints; list_empty]) ] in
    let listints2  = T [ ("nil", []); ("nil2", []); ("cons", [ ints; listints1]) ] in
    let pairs = T [ ("pair", [ listints2; listints2]) ] in
    let grounded = Typs.construct pairs in
    Typs.inject grounded

  let optimize = optimize_pair

  let prjp e =
    let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
    let prjl e =
      TwoNilList.L.prjc
        prj1
        (fun _ _ -> failwith "should not happen2")
        e
      in
    Std.Pair.prjc prjl prjl
      (fun _ _ -> failwith "should not happen5")
      e

  let wrap_demo demo_exprs =
    let open Unn_pre.Expr in
    let rec hack_list = function
    | TwoNilList.L.Nil -> econstr "nil" []
    | TwoNilList.L.Nil2 -> econstr "nil2" []
    | TwoNilList.L.Cons (_,tl) ->
        econstr "cons"  [ econstr "int" []; hack_list tl ]
    in
    ListLabels.map demo_exprs ~f:(fun (a,b) ->
      econstr "pair" [ hack_list a; hack_list b ]
    )


  let shortcut = simple_shortcut
end

module ArgTwoNilLists2Cons : ARG0 = struct
  include ArgTwoNilLists1

  let info = "two-nil lists (with cons)"

  let clauses =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 20
    ; ppair pnil2 pwc, IR.eint 30
    ; ppair pwc pnil2, IR.eint 40
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 60
    ]

end

module ArgTwoNilLists2Simplified : ARG0 = struct
  include ArgTwoNilLists1

  let info = "two-nil lists (with cons, simplified RHS)"

  let clauses =
    [ ppair pnil  pwc, IR.eint 10
    ; ppair pwc  pnil, IR.eint 10
    ; ppair pnil2 pwc, IR.eint 10
    ; ppair pwc pnil2, IR.eint 10
    ; ppair (pcons pwc pwc) (pcons pwc pwc), IR.eint 60
    ]

end

module ArgMake(Arg: ARG0) : ARG1 = struct
  include Arg

  let possible_answer : IR.ground =
    let run_ground clauses : IR.ground =
      let injected : Clauses.injected = Clauses.inject clauses in

      let first =
        OCanren.(run q (Work.compile_naively injected)) (fun rr -> rr#prj)
        |> OCanren.Stream.hd
      in
(*      print_endline "naive answer:";
      print_endline @@ IR.show first;*)
      let second = Arg.optimize first in
      (*print_endline "\noptimized answer:";
      print_endline @@ IR.show second;*)
      second
    in
    run_ground clauses

  let max_ifs_count = IR.count_ifs_ground possible_answer

  let ir_hint _ = OCanren.success
end

module type ARG_FINAL = sig
  include ARG1
end

