open Unn_pre

let simple_shortcut0 _ _ _ ans = OCanren.(ans === !!true)
let simple_shortcut _ _ _ _ ans = OCanren.(ans === !!true)
let simple_shortcut_tag _ _ ans = OCanren.(ans === !!true)

let inhabit_by typs cond =
  let open OCanren in
  let open Unn_pre in
  let module W = Unn_pre.WorkHO in
  let iter2io f =
    let rec helper n xs ys =
      conde
        [ xs === Std.List.nil () &&& (ys === Std.List.nil ())
        ; fresh (h1 tl1 h2 tl2)
            (xs === Std.(h1 % tl1))
            (ys === Std.(h2 % tl2))
            (f n h1 h2)
            (helper (N.s n) tl1 tl2) ] in
    helper N.(z) in
  let is_good_m m ans =
    fresh ()
      (debug_var m (flip Matchable.reify) (fun ms ->
           (*        Format.printf "default_shortcut0 on matchable %s\n%!" ((GT.show GT.list) Matchable.show_logic ms);*)
           match ms with
           | [] -> failure
           | _ :: _ :: _ -> failwith "too many answers"
           | [ms] -> (
             match Matchable.to_ground ms with
             | None ->
                 let _ = assert false in
                 success
             | Some _ ->
                 let b = cond ms in
                 ans === !!b )
           (* match Matchable.to_ground ms with
              | None ->
                  let _ = assert false in success
              | Some m ->
                let b = Pats_tree.is_set trie (Matchable.ground_to_list_repr m) in
                (*Format.printf " is_set %a = %b\n%!" (GT.fmt Matchable.ground) m b;*)
                (ans === !!b)*) ) )
      success in
  let rec helper m typs e =
    fresh (c es is_ok arg_typs) (is_good_m m is_ok)
      (conde
         [ fresh () (is_ok === !!true)
             (e === Expr.constr c es)
             (W.info_assoc typs c arg_typs)
             (iter2io (fun n -> helper (Matchable.field n m)) arg_typs es)
         ; fresh () (is_ok === !!false)
             (debug_var is_ok (flip OCanren.reify) (fun ok ->
                  let () =
                    match ok with [Value false] -> () | _ -> assert false in
                  only_head @@ W.well_typed_expr e typs !!true ) ) ] ) in
  helper (Matchable.scru ()) typs

let inhabit_by_trie typs trie =
  inhabit_by typs (fun ms ->
      match Matchable.to_ground ms with
      | None ->
          let _ = assert false in
          true
      | Some m ->
          let b = Pats_tree.is_set trie (Matchable.ground_to_list_repr m) in
          (*Format.printf " is_set %a = %b\n%!" (GT.fmt Matchable.ground) m b;*)
          b )

module type ARG0 = sig
  open OCanren

  type g
  type l
  type qtyp_injected = (g, l) injected

  val try_compile_naively : bool
  val inhabit : Expr.injected -> goal
  val clauses : Clauses.pre_ground
  val typs : Typs.ground
  val max_height : int
  val optimize : IR.ground -> IR.ground
  val initial_trie : Pats_tree.t

  val shortcut0 :
       Matchable.injected
    -> N.injected
    -> Cases.injected
    -> (bool, bool logic) injected
    -> goal

  val shortcut :
       Tag.injected
    -> Matchable.injected
    -> ( Tag.ground * IR.ground
       , (Tag.logic, IR.logic) Std.Pair.logic )
       Std.List.groundi
    -> (Matchable.ground, Matchable.logic) Std.List.groundi
    -> (bool, bool logic) injected
    -> goal

  val shortcut_tag :
    CNames.injected -> Cases.injected -> (bool, bool logic) injected -> goal

  val info : string
end

module type ARG_FINAL = sig
  include ARG0

  val possible_answer : IR.ground option

  (* maximum count of IFs in the example answer *)
  val max_ifs_count : int
  val minimal_trie : Pats_tree.t
  val max_examples_count : int
  val ir_hint : IR.injected -> OCanren.goal
  val max_nested_switches : int
end

module T = struct
  type t = (string * [`Other of t | `Self] list) list

  let list el = [("nil", []); ("cons", [`Other el; `Self])]

  let rec unfold depth (tt : t) : Unn_pre.Typs.pre_typ =
    let maptt f = List.map f tt in
    let rec helper depth =
      let open Unn_pre.Typs in
      if depth <= 0 then T []
      else
        T
          (maptt (fun (name, args) ->
               ( name
               , args
                 |> List.map (function
                      | `Self -> helper (depth - 1)
                      | `Other targ -> unfold (depth - 1) targ ) ) ) ) in
    helper depth
end

(* ************************************************************************** *)
module ArgTrueFalse : ARG0 = struct
  open OCanren

  type g = bool
  type l = bool logic
  type qtyp_injected = (g, l) OCanren.injected

  let info = "bool"

  let typs =
    let open Unn_pre.Typs in
    Typs.construct @@ T [("true", []); ("false", [])]

  let tt : T.t = [("true", []); ("false", [])]
  let typs = T.unfold 1 tt |> Typs.construct
  let clauses = [(ptrue, IR.eint 1); (pfalse, IR.eint 0)]
  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (1 = n);
    n

  let rec optimize (root : IR.ground) = root
  let prjp e = OCanren.prjc (fun _ _ -> failwith "should not happen5") e

  let to_expr (demo_exprs : bool list) =
    let open Unn_pre.Expr in
    let rec helper = function
      | true -> econstr "true" []
      | false -> econstr "false" [] in
    ListLabels.map demo_exprs ~f:helper

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

(* ************************************************************************** *)
module ArgAB : ARG0 = struct
  open OCanren

  type ab = A | B
  type g = ab
  type l = ab logic
  type qtyp_injected = (g, l) OCanren.injected

  let to_expr (demo_exprs : g list) =
    let open Unn_pre.Expr in
    let rec helper = function A -> econstr "A" [] | B -> econstr "B" [] in
    ListLabels.map demo_exprs ~f:helper

  let info = "A|B"
  let clauses = [(__, IR.eint 0); (pleaf "A", IR.eint 1)]

  let typs =
    let open Unn_pre.Typs in
    let grounded = Typs.construct @@ T [("A", []); ("B", [])] in
    grounded

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    assert (1 = n);
    n

  let rec optimize (root : IR.ground) = root
  let prjp e = OCanren.prjc (fun _ _ -> failwith "should not happen5") e
  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

(* ************************************************************************** *)
module ArgABC : ARG0 = struct
  open OCanren

  type abc = A | B | C
  type g = abc
  type l = abc logic
  type qtyp_injected = (g, l) OCanren.injected

  (* let to_expr (demo_exprs: g list) =
     let open Unn_pre.Expr in
     let rec helper = function
     | A  -> econstr "A" []
     | B  -> econstr "B" []
     | C  -> econstr "C" []
     in
     ListLabels.map demo_exprs ~f:helper*)

  let typs =
    let open Unn_pre.Typs in
    Typs.construct @@ T [("A", []); ("B", []); ("C", [])]

  let info = "A|B|C"

  let clauses =
    [(pleaf "A", IR.eint 1); (pleaf "B", IR.eint 1); (pleaf "C", IR.eint 0)]

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    assert (1 = n);
    n

  let rec optimize (root : IR.ground) = root
  let prjp e = OCanren.prjc (fun _ _ -> failwith "should not happen5") e
  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

(* ************************************************************************** *)
module ArgABCD : ARG0 = struct
  open OCanren

  type 'a txxx = C of 'a | A of 'a | B | D [@@deriving gt ~options:{gmap}]
  type g = g txxx
  type l = l txxx OCanren.logic

  module F = Fmap (struct
    type 'a t = 'a txxx

    let fmap eta = GT.gmap txxx eta
  end)

  type injected = (g, l) OCanren.injected
  type qtyp_injected = injected

  let c x : injected = inj @@ F.distrib (C x)
  let a x : injected = inj @@ F.distrib (A x)
  let b : injected = inj @@ F.distrib B
  let d : injected = inj @@ F.distrib D

  (* let to_expr (demo_exprs: g list) =
     let open Unn_pre.Expr in
     let rec helper = function
     | A x  -> econstr "A" [helper x]
     | B    -> econstr "B" []
     | C x  -> econstr "C" [helper x]
     | D    -> econstr "D" []
     in
     ListLabels.map demo_exprs ~f:helper*)

  let rec inhabit_t (rez : Expr.injected) : goal =
    conde
      [ (rez === Expr.(constr Tag.(inject @@ of_string_exn "D") Std.(nil ())))
      ; (rez === Expr.(constr Tag.(inject @@ of_string_exn "B") Std.(nil ())))
      ; fresh prev
          (rez === Expr.(constr Tag.(inject @@ of_string_exn "A") Std.(!<prev)))
          (inhabit_t prev)
      ; fresh prev
          (rez === Expr.(constr Tag.(inject @@ of_string_exn "C") Std.(!<prev)))
          (inhabit_t prev) ]

  let rec inhabit_height : Std.Nat.groundi -> Expr.injected -> goal =
   fun height rez ->
    conde
      [ Std.Nat.zero === height &&& failure
      ; fresh prev
          (Std.Nat.succ prev === height)
          (conde
             [ ( rez
               === Expr.(constr Tag.(inject @@ of_string_exn "D") Std.(nil ()))
               )
             ; ( rez
               === Expr.(constr Tag.(inject @@ of_string_exn "B") Std.(nil ()))
               )
             ; fresh inner
                 ( rez
                 === Expr.(
                       constr Tag.(inject @@ of_string_exn "A") Std.(!<inner))
                 )
                 (inhabit_height prev inner)
             ; fresh inner
                 ( rez
                 === Expr.(
                       constr Tag.(inject @@ of_string_exn "C") Std.(!<inner))
                 )
                 (inhabit_height prev inner) ] ) ]

  let inhabit n rez = inhabit_height (Std.nat n) rez
  let info = "A of t|B|C of t | D"

  let typs =
    let open Unn_pre.Typs in
    let l = T [("A", []); ("B", []); ("C", []); ("D", [])] in
    let l = T [("A", [l]); ("B", []); ("C", [l]); ("D", [])] in
    let l = T [("A", [l]); ("B", []); ("C", [l]); ("D", [])] in
    let l = T [("A", [l]); ("B", []); ("C", [l]); ("D", [])] in
    let l = T [("A", [l]); ("B", []); ("C", [l]); ("D", [])] in
    let l = T [("A", [l]); ("B", []); ("C", [l]); ("D", [])] in
    Typs.construct l

  let pa x = pconstr "A" [x]
  let pc x = pconstr "C" [x]
  let pb = pconstr "B" []
  let pd = pconstr "D" []
  let clauses = [(pc (pa pb), IR.eint 1); (pc __, IR.eint 2); (__, IR.eint 3)]
  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    assert (3 = n);
    n

  let rec optimize (root : IR.ground) = root
  let rec prjp e = F.prjc prjp (fun _ _ -> failwith "should not happen5") e
  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

let optimize_pair : IR.ground -> IR.ground =
 fun ir ->
  let open OCanren in
  let open Unn_pre.IR in
  let open Unn_pre.Matchable in
  (*
  GT.transform IR.ground
    (fun fself -> object
      inherit [_,_] IR.gmap_ground_t fself
      method! c_Switch acc me _m xs default =
        Format.printf "optimize_pair %a\n%!" (GT.fmt IR.ground) me;
        match xs with
        | Std.List.Nil -> fself () default
        | Std.List.Cons ( (t, then_), Std.List.Nil) when string_of_tag_exn t = "pair" -> fself () then_
        | _ -> fself () me
    end)
    ()
    ir
    *)

  (* I dont' know why but implementation above doesn't work (hangs) *)
  let rec helper = function
    | Lit n -> Lit n
    | Fail -> Fail
    | Switch (_, Std.List.Nil, default) -> helper default
    | Switch (_, Std.List.(Cons ((t, code), Nil)), _)
      when Tag.string_of_tag_exn t = "pair" ->
        helper code
    | Switch (m, xs, default) ->
        let ys = GT.gmap Std.List.ground (fun (t, c) -> (t, helper c)) xs in
        Switch (m, ys, helper default) in
  helper ir

let optimize_triple : IR.ground -> IR.ground =
 fun ir ->
  let open OCanren in
  let open Unn_pre.IR in
  let open Unn_pre.Matchable in
  let rec helper = function
    | Lit n -> Lit n
    | Fail -> Fail
    | Switch (_, Std.List.Nil, default) -> helper default
    | Switch (_, Std.List.(Cons ((t, code), Nil)), _)
      when Tag.string_of_tag_exn t = "triple" ->
        helper code
    | Switch (m, xs, default) ->
        let ys = GT.gmap Std.List.ground (fun (t, c) -> (t, helper c)) xs in
        Switch (m, ys, helper default) in
  helper ir

(* ************************************************************************** *)
module ArgPairTrueFalse : ARG0 = struct
  open OCanren

  type g = bool * bool
  type l = (bool logic, bool logic) Std.Pair.logic
  type qtyp_injected = (g, l) OCanren.injected

  let info = "bool*bool"

  let clauses =
    [ (ppair ptrue __, IR.eint 1); (ppair __ ptrue, IR.eint 1)
    ; (ppair pfalse pfalse, IR.eint 0) ]

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (2 = n);
    n

  let typs =
    let open Unn_pre.Typs in
    let bool = T [("true", []); ("false", [])] in
    let p = T [("pair", [bool; bool])] in
    Typs.construct p

  let tt : T.t =
    let bool_t = [("true", []); ("false", [])] in
    [("pair", [`Other bool_t; `Other bool_t])]

  let typs = T.unfold max_height tt |> Typs.construct
  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie
  let optimize = optimize_pair

  let prjp e =
    let prjl e =
      OCanren.prjc
        (fun _ _ -> failwiths "should not happen %s %d" __FILE__ __LINE__)
        e in
    Std.Pair.prjc prjl prjl
      (fun _ _ -> failwiths "should not happen %s %d" __FILE__ __LINE__)
      e

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

(* ************************************************************************** *)
module ArgTripleBool : ARG0 = struct
  open OCanren

  let info = "bool*bool*bool (Maranget;page1)"

  type g = bool * bool * bool
  type l = (bool logic, bool logic, bool logic) Triple.logic
  type qtyp_injected = (g, l) OCanren.injected

  let to_expr (demo_exprs : g list) =
    let open Unn_pre.Expr in
    let rec helper = function
      | true -> econstr "true" []
      | false -> econstr "false" [] in
    ListLabels.map demo_exprs ~f:(fun (a, b, c) ->
        econstr "triple" [helper a; helper b; helper c] )

  let clauses =
    [ (ptriple __ pfalse ptrue, IR.eint 1); (ptriple pfalse ptrue __, IR.eint 2)
    ; (ptriple __ __ pfalse, IR.eint 3); (ptriple __ __ ptrue, IR.eint 4) ]

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    assert (2 = n);
    n

  (* let typs =
     let open Unn_pre.Typs in
     let bool = T [("true", []); ("false", [])] in
     let p = T [("triple", [bool; bool; bool])] in
     Typs.construct p
  *)
  let tt : T.t =
    let bool_t = [("true", []); ("false", [])] in
    [("triple", [`Other bool_t; `Other bool_t; `Other bool_t])]

  let typs = T.unfold max_height tt |> Typs.construct
  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie
  let optimize = optimize_triple

  let prjp e =
    let prjl e =
      OCanren.prjc
        (fun _ _ -> failwiths "should not happen %s %d" __FILE__ __LINE__)
        e in
    Triple.prjc prjl prjl prjl
      (fun _ _ -> failwiths "should not happen %s %d" __FILE__ __LINE__)
      e

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

(* ************************************************************************** *)
let nat_inject =
  let open OCanren.Std in
  let rec helper = function
    | Nat.O -> Nat.zero
    | Nat.S xs -> Nat.succ (helper xs) in
  helper

module ArgPeanoSimple : ARG0 = struct
  open OCanren

  type g = (N.ground, N.ground) OCanren.Std.Pair.ground
  type l = (N.logic, N.logic) OCanren.Std.Pair.logic
  type qtyp_injected = (g, l) OCanren.injected

  let rec all_inhabitants (rez : N.injected) =
    conde [rez === N.z; fresh (size_tl tl) (N.s tl === rez) (all_inhabitants tl)]

  let make_wildcard_inhabitant : N.ground =
    let open OCanren in
    run q all_inhabitants (fun rr ->
        rr#prjc @@ N.prjc (fun _ _ -> assert false) )
    |> OCanren.Stream.hd

  let for_wildcard = make_wildcard_inhabitant

  let typs =
    let open Unn_pre.Typs in
    let make prev = T [("zero", []); ("succ", [prev])] in
    let empty = T [("zero", [])] in
    let height = make empty in
    let height = make height in
    let height = make height in
    let pairs = T [("pair", [height; height])] in
    Typs.construct pairs

  let info = "simple nats (a la Maranget2008)"

  let clauses =
    [ (ppair (psucc __) (psucc __), IR.eint 30); (ppair pzero __, IR.eint 10)
    ; (ppair __ pzero, IR.eint 10) ]

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (2 = n);
    n

  let optimize = optimize_pair
  (*
  let prjp e =
    let prjl e =
      N.prjc
        (fun _ _ -> failwiths "should not happen %s %d" __FILE__ __LINE__)
        e
      in
    Std.Pair.prjc prjl prjl
      (fun _ _ -> failwiths "should not happen5 %s %d" __FILE__ __LINE__)
      e

  let to_expr (demo_exprs: (N.ground * N.ground) list) =
    let open Unn_pre.Expr in
    let rec helper = function
    | N.Z -> econstr "zero" []
    | N.S tl ->
        econstr "succ" [ helper tl ]
    in
    ListLabels.map demo_exprs ~f:(fun (a,b) ->
      econstr "pair" [ helper a; helper b ]
    )*)

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

let list_inject arg =
  let open OCanren.Std in
  let rec helper = function
    | List.Nil -> nil ()
    | List.Cons (x, xs) -> arg x % helper xs in
  helper

module ArgSimpleList : ARG0 = struct
  open OCanren

  type g = (int Std.List.ground, int Std.List.ground) Std.Pair.ground
  type l = (int logic Std.List.logic, int logic Std.List.logic) Std.Pair.logic
  type qtyp_injected = (g, l) injected

  let typs =
    let open Unn_pre.Typs in
    let ints = T [("int", [])] in
    let list_empty = T [("nil", [])] in
    let listints1 = T [("nil", []); ("cons", [ints; list_empty])] in
    let listints2 = T [("nil", []); ("cons", [ints; listints1])] in
    let pairs = T [("pair", [listints2; listints2])] in
    let grounded = Typs.construct pairs in
    grounded

  let info = "simple lists (from Maranget2008)"

  let clauses =
    [ (ppair pnil __, IR.eint 10); (ppair __ pnil, IR.eint 20)
    ; (ppair (pcons __ __) (pcons __ __), IR.eint 30) ]

  (*
  let rec all_inhabitants inh_arg rez =
    conde
      [ (rez === Std.List.nil ())
      ; fresh (x tl)
          (Std.List.cons x tl === rez)
          (inh_arg x)
          (all_inhabitants inh_arg tl)
      ]

  let make_wildcard_inhabitant on_arg: Expr.ground =
    run q (fun q -> Work.well_typed_expr q on_arg !!true)
      (fun rr -> rr#prjc Expr.prjc)
      |> OCanren.Stream.hd

  let for_wildcard = make_wildcard_inhabitant (fun q -> (q=== Expr.constr !!"one" (Std.List.nil())))*)

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  (*
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
    let default = (make_wildcard_inhabitant inh_arg) in
    conde
      [ (Std.Nat.zero === height) &&& (r === list_inject (!!) default)
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
*)

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (2 = n);
    n

  let optimize = optimize_pair

  module L = OCanren.Std.List

  let prjp e =
    let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
    let prjl e = L.prjc prj1 (fun _ _ -> failwith "should not happen2") e in
    Std.Pair.prjc prjl prjl (fun _ _ -> failwith "should not happen5") e
  (*
  let to_expr demo_exprs =
    let open Unn_pre.Expr in
    let rec hack_list = function
    | L.Nil -> econstr "nil" []
    | L.Cons (_,tl) ->
        econstr "cons"  [ econstr "int" []; hack_list tl ]
    in
    ListLabels.map demo_exprs ~f:(fun (a,b) ->
      econstr "pair" [ hack_list a; hack_list b ]
    )*)

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

module TwoNilList = struct
  open Helper
  open OCanren

  module L = struct
    type ('a, 'self) t = Nil | Nil2 | Cons of 'a * 'self
    [@@deriving gt ~options:{show; fmt; gmap}]

    type 'a ground = ('a, 'a ground) t
    [@@deriving gt ~options:{show; fmt; gmap}]

    type 'a logic = ('a, 'a logic) t OCanren.logic
    [@@deriving gt ~options:{show; fmt; gmap}]

    type ('a, 'b) injected = ('a ground, 'b logic) OCanren.injected

    module T = Fmap2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let fmap fa fb = (GT.gmap t) fa fb
    end)

    let nil () = inj @@ T.distrib Nil
    let nil2 () = inj @@ T.distrib Nil2
    let cons x xs = inj @@ T.distrib @@ Cons (x, xs)
    let rec reify r1 h = T.reify r1 (reify r1) h
    let rec prjc fa onvar env xs = T.prjc fa (prjc fa onvar) onvar env xs

    let inject arg (e : _ ground) : (_, _) injected =
      let rec helper = function
        | Nil -> nil ()
        | Nil2 -> nil2 ()
        | Cons (x, xs) -> cons (arg x) (helper xs) in
      helper e
  end

  (*
  let wrap root: Expr.ground =
    let open Expr in
    let rec helper = function
    | L.Nil -> Expr.econstr "nil" []
    | L.Nil2 -> Expr.econstr "nil2" []
    | L.Cons (_,tl) ->
        econstr "cons" [ econstr "int" []; helper tl ]
    in
    helper root
*)
  let rec all_inhabitants_2nillist inh_arg rez =
    conde
      [ rez === L.nil (); rez === L.nil2 ()
      ; fresh (x tl)
          (L.cons x tl === rez)
          (inh_arg x)
          (all_inhabitants_2nillist inh_arg tl) ]
  (*
  let () =
    let open Mytester in
    let show = GT.(show L.ground @@ show int) in
    let showl = GT.(show L.logic (show OCanren.logic @@ show int)) in
    runR (L.reify OCanren.reify) show showl  1 q qh
      ("wtf", all_inhabitants_2nillist (fun _ -> success))
*)

  (*
  let make_wildcard_inhabitant on_arg: _ L.ground =
    run q (all_inhabitants_2nillist on_arg)
      (fun rr -> rr#prjc @@ L.prjc
          (fun _ _ -> failwith "A")
              (fun _ _ -> failwith "B")
      )
      |> OCanren.Stream.hd

  let for_wildcard = make_wildcard_inhabitant (fun q -> (q=== Expr.constr !!"one" (Std.List.nil())))

  let rec inhabit_twonil_list :
      Std.Nat.groundi ->
      (('a, 'b) OCanren.injected -> goal) ->
      ('a, 'b) L.injected ->
      goal
    = fun height inh_arg r ->

    let default = (make_wildcard_inhabitant inh_arg) in
    conde
      [ (Std.Nat.zero === height) &&& (r === L.inject (!!) default)
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
*)
end

(* ************************************************************************** *)
module ArgTwoNilLists1 : ARG0 = struct
  open OCanren

  type g =
    (int TwoNilList.L.ground, int TwoNilList.L.ground) OCanren.Std.Pair.ground

  type l =
    ( int OCanren.logic TwoNilList.L.logic
    , int OCanren.logic TwoNilList.L.logic )
    OCanren.Std.Pair.logic

  type qtyp_injected = (g, l) OCanren.injected

  let info = "two-nil lists (no cons -- use WCs)"

  let typs =
    let open Unn_pre in
    let open Unn_pre.Typs in
    let ints = T [("int", [])] in
    let lists = T [("nil", []); ("nil2", [])] in
    let lists = T [("nil", []); ("nil2", []); ("cons", [ints; lists])] in
    let lists = T [("nil", []); ("nil2", []); ("cons", [ints; lists])] in
    let pairs = T [("pair", [lists; lists])] in
    let grounded = Typs.construct pairs in
    grounded

  let clauses =
    [ (ppair pnil __, IR.eint 10); (ppair __ pnil, IR.eint 20)
    ; (ppair pnil2 __, IR.eint 30); (ppair __ pnil2, IR.eint 40)
    ; (ppair __ __, IR.eint 60) ]

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    (*    Format.printf "patterns max height = %d\n%!" n;*)
    assert (2 = n);
    n

  let optimize = optimize_pair

  let prjp e =
    let prj1 e = OCanren.prjc (fun _ _ -> failwith "should not happen") e in
    let prjl e =
      TwoNilList.L.prjc prj1 (fun _ _ -> failwith "should not happen2") e in
    Std.Pair.prjc prjl prjl (fun _ _ -> failwith "should not happen5") e

  let to_expr demo_exprs =
    let open Unn_pre.Expr in
    let rec hack_list = function
      | TwoNilList.L.Nil -> econstr "nil" []
      | TwoNilList.L.Nil2 -> econstr "nil2" []
      | TwoNilList.L.Cons (_, tl) ->
          econstr "cons" [econstr "int" []; hack_list tl] in
    ListLabels.map demo_exprs ~f:(fun (a, b) ->
        econstr "pair" [hack_list a; hack_list b] )

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = true
end

module ArgTwoNilLists2Cons : ARG0 = struct
  include ArgTwoNilLists1

  let info = "two-nil lists (with cons)"

  let clauses =
    [ (ppair pnil __, IR.eint 10); (ppair __ pnil, IR.eint 20)
    ; (ppair pnil2 __, IR.eint 30); (ppair __ pnil2, IR.eint 40)
    ; (ppair (pcons __ __) (pcons __ __), IR.eint 60) ]
end

module ArgTwoNilLists2Simplified : ARG0 = struct
  include ArgTwoNilLists1

  let info = "two-nil lists (with cons; simplified RHS)"

  let clauses =
    [ (ppair pnil __, IR.eint 10); (ppair __ pnil, IR.eint 10)
    ; (ppair pnil2 __, IR.eint 10); (ppair __ pnil2, IR.eint 10)
    ; (ppair (pcons __ __) (pcons __ __), IR.eint 60) ]

  let () = assert (max_height = 2)
end

module PCF = struct
  type code =
    | Ldi of int
    | Search of int
    | Mkclos of int
    | Mkclosrec of int
    | IOp of int
    | Int of int
    | Test of int * int
    | Clo of int * int
    | Push
    | Extend
    | Pushenv
    | Popenv
    | Apply

  type acc = code
  type stack_item = Val of code | Env of int | Code of int

  module S : sig
    val run : acc -> stack_item list -> code list -> int
  end = struct
    let rec run a s c =
      match (a, s, c) with
      | _, _, Ldi i :: c -> 1
      | _, _, Push :: c -> 2
      | Int n2, Val (Int n1) :: s, IOp op :: c -> 3
      | Int 0, _, Test (c2, _) :: c -> 4
      | Int _, _, Test (_, c3) :: c -> 5
      | _, _, Extend :: c -> 6
      | _, _, Search k :: c -> 7
      | _, _, Pushenv :: c -> 8
      | _, Env e :: s, Popenv :: c -> 9
      | _, _, Mkclos cc :: c -> 10
      | _, _, Mkclosrec cc :: c -> 11
      | Clo (cc, ce), Val v :: s, Apply :: c -> 12
      | a, Code c :: Env e :: s, [] -> 13
      | a, [], [] -> 14
  end
  [@warning "-8"]
end

module ArgPCF : ARG0 = struct
  open OCanren

  type g
  type l
  type qtyp_injected = (g, l) OCanren.injected

  let info = "BIG (no cons -- use WCs)"
  let pldi x = pconstr "Ldi" [x]
  let psearch x = pconstr "Search" [x]
  let ppush = pconstr "Push" []
  let ppushenv = pconstr "Pushenv" []
  let ppopenv = pconstr "Popenv" []
  let pextend = pconstr "Extend" []
  let papply = pconstr "Apply" []
  let pmkclos x = pconstr "Mkclos" [x]
  let pmkclosrec x = pconstr "Mkclosrec" [x]
  let pInt x = pconstr "Int" [x]
  let pval x = pconstr "Val" [x]
  let piop x = pconstr "IOp" [x]
  let ptest x y = pconstr "Test" [x; y]
  let pclo x y = pconstr "Clo" [x; y]
  let pval x = pconstr "Val" [x]
  let penv x = pconstr "Env" [x]
  let pcode x = pconstr "Code" [x]

  let clauses =
    [ (ptriple __ __ (pcons (pldi __) __), IR.eint 1)
    ; (ptriple __ __ (pcons ppush __), IR.eint 2)
    ; (ptriple (pInt __) __ (pcons (piop __) __), IR.eint 3)
      (*    ; ptriple (pInt __) (pcons (pval __) __) (pcons (piop __) __), IR.eint 3*)
      (*    ; ptriple (pInt __) (pcons (pval (pInt __)) __)  (pcons (piop __) __), IR.eint 3*)
      (*    ; ptriple (pInt __) (pcons __ __)  (pcons (piop __) __), IR.eint 3*)

      (*    ; ptriple (pInt __) __  (pcons __ __), IR.eint 3*)

      (* ; ptriple (pInt __) __              (pcons (ptest __ __) __), IR.eint 4

         ; ptriple __   __ (pcons pextend __), IR.eint 6
         ; ptriple __   __ (pcons (psearch __) __), IR.eint 7
         ; ptriple __   __ (pcons ppushenv __), IR.eint 8
         ; ptriple __   (pcons (penv __) __) (pcons ppopenv __), IR.eint 9
         ; ptriple __   __ (pcons (pmkclos __) __), IR.eint 10
         ; ptriple __   __ (pcons (pmkclosrec __) __), IR.eint 10
         ; ptriple (pclo __ __) (pcons (pval __) __) (pcons papply __), IR.eint 12
         ; ptriple __   (pcons (pcode __) (pcons (penv __) __)) pnil, IR.eint 13
         ; ptriple __   pnil pnil, IR.eint 14*) ]

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    n

  let typs =
    let open Unn_pre in
    let open Unn_pre.Typs in
    let int = T [("42", [])] in
    (*    let pairint = T [ ("pair", [ int; int ]) ] in*)
    let code =
      T
        [ ("Push", [])
          (* ; ("Extend", [])
             ; ("Pushenv", [])
             ; ("Popenv", [])
             ; ("Apply", [])*)
        ; ("Ldi", [int])
          (* ; ("Search", [ int ])
             ; ("Mkclos", [ int ])
             ; ("Mkclosrec", [ int ])*); ("IOp", [int]); ("Int", [int])
          (* ; ("Test", [ int; int ])
             ; ("Clo", [ int; int])*) ] in
    let prog =
      let t = T [("nil", [])] in
      let t = T [("nil", []); ("cons", [code; t])] in
      let t = T [("nil", []); ("cons", [code; t])] in
      let t = T [("nil", []); ("cons", [code; t])] in
      t in
    let stack_item = T [("Val", [code]); ("Env", [int]); ("Code", [int])] in
    let stack =
      let t = T [("nil", [])] in
      let t = T [("nil", []); ("cons", [stack_item; t])] in
      let t = T [("nil", []); ("cons", [stack_item; t])] in
      let t = T [("nil", []); ("cons", [stack_item; t])] in
      t in
    let pairs = T [("triple", [code; stack; prog])] in
    let grounded = Typs.construct pairs in
    grounded

  let tts : T.t =
    let int = [("42", [])] in
    let code =
      [ ("Push", []); ("Ldi", [`Other int]); ("IOp", [`Other int])
      ; ("Int", [`Other int]) ] in
    let prog = T.list code in
    let stack_item =
      [("Val", [`Other code]); ("Env", [`Other int]); ("Code", [`Other int])]
    in
    let stack = T.list stack_item in
    [("triple", [`Other code; `Other stack; `Other prog])]

  (*  let () = print_endline @@ GT.show Unn_pre.Typs.ground typs*)
  let typs = Unn_pre.Typs.construct @@ T.unfold (1 + max_height) tts

  (* let () = print_endline @@ GT.show Unn_pre.Typs.ground typs *)

  let inhabit n e =
    Work_base_common.well_typed_expr_height
      N.(inject @@ of_int n)
      Expr.(inject @@ eleaf "nil")
      e (Typs.inject typs) !!true

  let _f () =
    let open OCanren in
    let r =
      inhabit_by (Typs.inject typs) (fun ms ->
          let h = Matchable.low_height_of_logic ms in
          if h > max_height + 1 then false else true ) in
    let s = run q r (fun rr -> rr#reify Expr.reify) in
    let xs = Stream.take s in
    let n = List.length xs in
    Printf.printf
      "With default generation there are %d examples for test `%s`\n%!" n info;
    Printf.printf "<examples>\n%!";
    List.iteri (fun i e -> Printf.printf "\t%d: %s\n" i (Expr.show_logic e)) xs;
    Printf.printf "</examples>\n%!"

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie
  let optimize = optimize_pair
  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = false
end

module ArgTuple5 : ARG0 = struct
  open OCanren

  type g
  type l
  type qtyp_injected = (g, l) OCanren.injected

  let info = "for path heuristic (no cons -- use WCs)"

  let typs =
    let open Unn_pre in
    let open Unn_pre.Typs in
    (*    let int = T [ ("int",[]) ] in*)
    let list_item =
      T
        [ ("Push", []); ("Extend", []) (*      ; ("Pushenv", [])*)
          (*      ; ("Popenv", [])*)
          (*      ; ("Apply", [])*)
          (*; ("Ldi", [ int ])
            ; ("Search", [ int ])
            ; ("Mkclos", [ int ])
            ; ("Mkclosrec", [ int ])
            ; ("IOp", [ int ])
            ; ("Int", [ int ])
            ; ("Test", [ int ])
            ; ("Clo", [ int ])*) ] in
    let stack =
      let t = T [("nil", [])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      let t = T [("nil", []); ("cons", [list_item; t])] in
      t in
    let pairs = T [("triple", [stack; stack; stack])] in
    Typs.construct pairs

  let pldi x = pconstr "Ldi" [x]
  let psearch x = pconstr "Search" [x]
  let ppush = pconstr "Push" []
  let ppushenv = pconstr "Pushenv" []
  let ppopenv = pconstr "Popenv" []
  let pextend = pconstr "Extend" []
  let papply = pconstr "Apply" []
  let pmkclos x = pconstr "Mkclos" [x]
  let pmkclosrec x = pconstr "Mkclosrec" [x]
  let pint x = pconstr "Int" [x]
  let pval x = pconstr "Val" [x]
  let piop x = pconstr "IOp" [x]
  let ptest x y = pconstr "Test" [x; y]
  let pclo x y = pconstr "Clo" [x; y]
  let pval x = pconstr "Val" [x]
  let penv x = pconstr "Env" [x]
  let pcode x = pconstr "Code" [x]
  let optimize = id

  let clauses =
    [ (ptriple __ __ (pcons __ (pcons __ (pcons __ __))), IR.eint 1)
    ; (ptriple __ __ (pcons ppush __), IR.eint 2) ]

  let initial_trie = Pats_tree.build clauses typs
  let inhabit = inhabit_by_trie (Typs.inject typs) initial_trie

  let max_height =
    let n =
      Helper.List.max (List.map (fun (p, _) -> Pattern.height p) clauses) in
    n

  let shortcut0 = simple_shortcut0
  let shortcut = simple_shortcut
  let shortcut_tag = simple_shortcut_tag
  let try_compile_naively = false
end

module ArgMake (Arg : ARG0) : ARG_FINAL = struct
  include Arg

  let possible_answer, max_ifs_count =
    if Arg.try_compile_naively then
      let run_ground clauses : IR.ground =
        let injected : Clauses.injected = Clauses.inject clauses in
        let first =
          OCanren.(run q (Work_base_common.compile_naively injected)) (fun rr ->
              rr#prj )
          |> OCanren.Stream.hd in
        let second = Arg.optimize first in
        second in
      let ans = run_ground clauses in
      (Some ans, IR.count_ifs_ground ans)
    else
      let sum =
        List.fold_left
          (fun acc (p, _) -> acc + Pattern.count_constructors p)
          0 clauses in
      (None, sum)

  let minimal_trie = Pats_tree.minimize initial_trie
  let ir_hint _ = OCanren.success
  let max_examples_count = -1

  let max_nested_switches : int =
    List.map
      (fun (p, _) ->
        GT.transform Pattern.ground
          (fun fself ->
            object
              method c_PConstr acc _ name args =
                GT.foldl OCanren.Std.List.ground fself (1 + acc) args

              method c_WildCard acc _ = acc + 1
            end )
          0 p
        |> fun size ->
        (*        Format.printf "pattern %a has size %d\n%!" (GT.fmt Pattern.ground) p size;*)
        size )
      clauses
    |> Helper.List.max
end

module type ALGO = sig
  module Make : functor (W : WORK) (Arg : ARG_FINAL) -> sig
    val test :
         ?print_examples:bool
      -> ?debug_filtered_by_size:bool
      -> ?with_hack:bool
      -> ?check_repeated_ifs:bool
      -> ?prunes_period:int option
      -> ?with_default_shortcuts:bool
      -> int
      -> unit
  end
end
