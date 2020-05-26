open OCanren
open Helper

let () =
  run one inhabit_int (fun r -> r#reify OCanren.reify)
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list) GT.(fmt OCanren.logic @@ fmt int) Format.std_formatter;
  Format.printf "\n%!"

let () =
  run one inhabit_bool (fun r -> r#reify OCanren.reify)
    |> OCanren.Stream.take ~n:(-1)
    |> GT.(fmt list) GT.(fmt OCanren.logic @@ fmt bool) Format.std_formatter;
  Format.printf "\n%!"


(* ********************************************************************** *)
module Test1 = struct
  type _ expr =
    | Int  : int -> int expr
    | Bool : bool -> bool expr
    | If   : bool expr * 'a expr * 'a expr -> 'a expr

  module GExpr = struct
    type ('int, 'bool, 'self) g =
      | Int of 'int
      | Bool of 'bool
      | If of 'self * 'self * 'self [@@deriving gt ~options:{gmap; fmt }]

    type ground = (int, bool, ground) g
    type logic  = (GT.int OCanren.logic, GT.bool OCanren.logic, logic) g OCanren.logic
      [@@deriving gt ~options:{ fmt }]
    type inj = (ground, logic) injected

    module F = Fmap3(struct
      type ('a,'b,'c) t = ('a,'b,'c) g
      let fmap p q r x = (GT.gmap g) p q r x
    end)

    let rec reify env x = F.reify OCanren.reify OCanren.reify reify env x

    let int x : (_,_) injected = inj @@ F.distrib @@ Int x
    let bool b      = inj @@ F.distrib @@ Bool b
    let if_ c th el = inj @@ F.distrib @@ If (c, th, el)
  end


  let rec inhabit_expr : 'a 'b .
      (('a, 'b) OCanren.injected -> goal) ->
      Info.inj ->
      GExpr.inj ->
      goal
    = fun inh_arg arg_desc r ->
    let open GExpr in
    conde
      [ fresh (i)
          (Info.leaf !!"int" === arg_desc)
          (int i === r)
          (inhabit_int i)
      ; fresh (b)
          (Info.leaf !!"bool" === arg_desc)
          (bool b === r)
          (inhabit_bool b)
      ; fresh (c th el)
          (if_ c th el === r)
          (inhabit_expr inhabit_bool (Info.leaf !!"bool") c)
          (inhabit_expr inh_arg arg_desc th)
          (inhabit_expr inh_arg arg_desc el)
      ]


  (* Tests *)

  (* int expr *)
  let _f  =
    run one (inhabit_expr inhabit_int (Info.leaf !!"int") )
      (fun r -> r#reify GExpr.reify)
    |> OCanren.Stream.mapi (fun i x ->
           Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
         )
    |> OCanren.Stream.take ~n:10 |> ignore;
    Format.printf "\n%!"
    (*
    0:      Int (1)
    1:      If (Bool (false), Int (1), Int (1))
    2:      If (Bool (true), Int (1), Int (1))
    3:      If (Bool (false), Int (1), If (Bool (false), Int (1), Int (1)))
    4:      If (Bool (false), If (Bool (false), Int (1), Int (1)), Int (1))
    5:      If (Bool (false), Int (1), If (Bool (true), Int (1), Int (1)))
    6:      If (If (Bool (false), Bool (false), Bool (false)), Int (1), Int (1))
    7:      If (Bool (true), Int (1), If (Bool (false), Int (1), Int (1)))
    8:      If (Bool (true), If (Bool (false), Int (1), Int (1)), Int (1))
    9:      If (Bool (false), If (Bool (true), Int (1), Int (1)), Int (1))

    *)

  (* bool expr *)
  let _bool  =
    run one (inhabit_expr inhabit_int (Info.leaf !!"bool") )
      (fun r -> r#reify GExpr.reify)
    |> OCanren.Stream.mapi (fun i x ->
           Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
         )
    |> OCanren.Stream.take ~n:20 |> ignore;
    Format.printf "\n%!"
    (*
    0:      Bool (false)
    1:      Bool (true)
    2:      If (Bool (false), Bool (false), Bool (false))
    3:      If (Bool (false), Bool (false), Bool (true))
    4:      If (Bool (false), Bool (true), Bool (false))
    5:      If (Bool (true), Bool (false), Bool (false))
    6:      If (Bool (false), Bool (true), Bool (true))
    7:      If (Bool (true), Bool (false), Bool (true))
    8:      If (Bool (true), Bool (true), Bool (false))
    9:      If (Bool (true), Bool (true), Bool (true))
    10:     If (Bool (false), Bool (false), If (Bool (false), Bool (false), Bool (false))
       )
    11:     If (Bool (false), Bool (false), If (Bool (false), Bool (false), Bool (true)))
    12:     If (If (Bool (false), Bool (false), Bool (false)), Bool (false), Bool (false)
       )
    13:     If (Bool (false), Bool (false), If (Bool (false), Bool (true), Bool (false)))
    14:     If (If (Bool (false), Bool (false), Bool (false)), Bool (false), Bool (true))
    15:     If (Bool (false), Bool (false), If (Bool (true), Bool (false), Bool (false)))
    16:     If (Bool (false), Bool (false), If (Bool (false), Bool (true), Bool (true)))
    17:     If (Bool (false), Bool (true), If (Bool (false), Bool (false), Bool (false)))
    18:     If (Bool (true), Bool (false), If (Bool (false), Bool (false), Bool (false)))
    19:     If (Bool (false), Bool (false), If (Bool (true), Bool (false), Bool (true)))
    *)

  (* string expr hangs *)
  let _hangs () =
    run one (inhabit_expr inhabit_int (Info.leaf !!"string") )
      (fun r -> r#reify GExpr.reify)
    |> OCanren.Stream.mapi (fun i x ->
           Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
         )
    |> OCanren.Stream.take ~n:1 |> ignore;
    Format.printf "\n%!"



  (* 'a expr *)
  let _fresh  =
    run one (fun r -> fresh (x) (inhabit_expr inhabit_int x r))
      (fun r -> r#reify GExpr.reify)
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
       )
    |> OCanren.Stream.take ~n:20 |> ignore;
    Format.printf "\n%!"
    (*
    0:      Int (1)
    1:      Bool (false)
    2:      Bool (true)
    3:      If (Bool (false), Int (1), Int (1))
    4:      If (Bool (true), Int (1), Int (1))
    5:      If (Bool (false), Bool (false), Bool (false))
    6:      If (Bool (false), Bool (false), Bool (true))
    7:      If (Bool (false), Int (1), If (Bool (false), Int (1), Int (1)))
    8:      If (Bool (false), Bool (true), Bool (false))
    9:      If (Bool (true), Bool (false), Bool (false))
    10:     If (Bool (false), Bool (true), Bool (true))
    11:     If (Bool (true), Bool (false), Bool (true))
    12:     If (Bool (false), Int (1), If (Bool (true), Int (1), Int (1)))
    13:     If (If (Bool (false), Bool (false), Bool (false)), Int (1), Int (1))
    14:     If (Bool (true), Int (1), If (Bool (false), Int (1), Int (1)))
    15:     If (Bool (true), Bool (true), Bool (false))
    16:     If (Bool (true), Bool (true), Bool (true))
    17:     If (If (Bool (false), Bool (false), Bool (true)), Int (1), Int (1))
    18:     If (Bool (false), Bool (false), If (Bool (false), Bool (false), Bool (false)))
    19:     If (Bool (true), Int (1), If (Bool (true), Int (1), Int (1)))
    *)
end

module Test2 = struct
  type _ choice =
    | Int  : 'blackbox -> int choice
    | Bool : 'blackbox -> bool choice
    | A    : 'a -> 'a choice

  module GChoice = struct
    type 'a g =
      | Int  of 'a
      | Bool of 'a
      | A    of 'a
    [@@deriving gt ~options:{gmap; fmt }]

    type 'a ground = 'a g
    type 'a logic  = 'a g OCanren.logic
      [@@deriving gt ~options:{ fmt }]
    type ('a,'b) inj = ('a ground, 'b logic) OCanren.injected

    module F = Fmap(struct
      type 'a t = 'a g
      let fmap p x = (GT.gmap g) p x
    end)

    let reify f env x = F.reify f env x

    let int x : (_,_) injected = inj @@ F.distrib @@ Int x
    let bool b      = inj @@ F.distrib @@ Bool b
    let a    b      = inj @@ F.distrib @@ A b
  end

  let rec inhabit_choice : 'a 'b .
      (('a, 'b) OCanren.injected -> goal) ->
      Info.inj ->
      ('a, 'b) GChoice.inj ->
      goal
    = fun inh_arg arg_desc r ->
    let open GChoice in
    conde
      [ fresh (i)
          (Info.leaf !!"int" === arg_desc)
          (r === int i)
        (*  (inh_arg i)*)
      ; fresh (b)
          (Info.leaf !!"bool" === arg_desc)
          (r === bool b)
        (*  (inh_arg b)*)
      ; fresh (arg x)
          (arg === arg_desc)
          (r === a x)
          (inh_arg x)
      ]


  (* 'a choice *)
  let () =
    run one (fun r -> fresh (x) (inhabit_choice inhabit_free x r))
      (fun r -> r#reify (GChoice.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt GChoice.logic @@ (fmt OCanren.logic @@ fmt int)) x
       )
    |> OCanren.Stream.take ~n:(-1) |> ignore
    ;
    Format.printf "\n%!"
    (*
    0:      Int (_.12)
    1:      Bool (_.13)
    2:      A (_.15)
    *)

  (* int choice *)
  let () =
    run one (fun r -> inhabit_choice inhabit_int Info.int r)
      (fun r -> r#reify (GChoice.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt GChoice.logic @@ (fmt OCanren.logic @@ fmt int)) x
       )
    |> OCanren.Stream.take ~n:(-1) |> ignore
    ;
    Format.printf "\n%!"
    (*
      0:      Int (_.11)
      1:      A (1)
    *)

  (* bool choice *)
  let () =
    run one (fun r -> inhabit_choice inhabit_bool Info.bool r)
      (fun r -> r#reify (GChoice.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt GChoice.logic @@ (fmt OCanren.logic @@ fmt bool)) x
       )
    |> OCanren.Stream.take ~n:(-1) |> ignore
    ;
    Format.printf "\n%!"
    (*
      0:      Bool (_.12)
      1:      A (false)
      2:      A (true)
    *)
end


module Test3 = struct
  type 'a s = S  (* abstract type will not work *)
  type z

  type ('a, 'size) vector =
    | VNil  : ('a, z) vector
    | VCons : 'a * ('a, 'size) vector -> ('a, 'size s) vector

  module GVector = OCanren.Std.List

  let rec inhabit_vector : 'a 'b .
      (('a, 'b) OCanren.injected -> goal) ->
      arg_desc: Info.inj ->
      size_desc:Info.inj ->
      ('a, 'b) GVector.groundi ->
      goal
    = fun inh_arg ~arg_desc ~size_desc r ->
    conde
      [ fresh (i)
          (Info.leaf !!"z" === size_desc)
          (r === Std.nil ())
      ; fresh (size_tl h tl)
          (Info.complex !!"s" Std.List.(!< size_tl) === size_desc)
          (Std.List.cons h tl === r)
          (inh_arg h)
          (inhabit_vector inh_arg ~arg_desc ~size_desc:size_tl  tl)
(*
      ; fresh (b)
          (Info.leaf !!"bool" === arg_desc)
          (r === bool b)
        (*  (inh_arg b)*)
      ; fresh (arg x)
          (arg === arg_desc)
          (r === a x)
          (inh_arg x)*)
      ]

  let () =
    run one (inhabit_vector inhabit_bool ~arg_desc:Info.bool ~size_desc:Info.size3)
      (fun r -> r#reify (GVector.reify OCanren.reify))
    |> OCanren.Stream.mapi (fun i x ->
         Format.printf "%d:\t%a\n%!" i GT.(fmt GVector.logic @@ (fmt OCanren.logic @@ fmt bool)) x
       )
    |> OCanren.Stream.take ~n:(-1) |> ignore
    ;
    Format.printf "\n%!"
end

(* About bivariance https://github.com/ocaml/ocaml/issues/5985
    bivariant (= irrelevant) types ('a t) have the distinct property that the equation
    (foo t = bar t) does not necessarily implies (foo = bar), while types
    of any other variance do.

    type 'a s = int (* is bivariant *)
*)


