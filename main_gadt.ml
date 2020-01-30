open Printf 

let () = 
  Printf.printf "main_gadt\n%!"

open OCanren 

let inhabit_int r = (r === !!1)
let inhabit_bool r = conde [ r=== !!false; r === !!true ]

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
type 'a expr = 
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

module Info = struct 
  type ('string, 'xs) ginfo = Complex of 'string * 'xs 
    [@@deriving gt ~options:{gmap; fmt }]
  module F = Fmap2(struct 
    type ('a, 'b) t = ('a, 'b) ginfo
    let fmap p q x = (GT.gmap ginfo) p q x
  end)

  type ground = (GT.string,              ground Std.List.ground) ginfo 
  type logic  = (GT.string OCanren.logic, logic Std.List.logic) ginfo OCanren.logic
    [@@deriving gt ~options:{fmt}]
    
  type inj = (ground, logic) OCanren.injected 

  let rec reify env (x: inj) : logic = F.reify OCanren.reify (Std.List.reify reify) env x

  let complex name xs = inj @@ F.distrib (Complex (name,xs))
  let leaf name : inj = complex name (Std.List.nil())
   
  let int = leaf !!"int"
  let bool = leaf !!"bool"

  let test _ = 
    run one (fun q -> (q === leaf !!"int"))
      (fun r -> r#reify reify)
      |> OCanren.Stream.take ~n:(-1)
      |> GT.(fmt list) GT.(fmt logic) Format.std_formatter;
    Format.printf "\n%!"
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
        (r === int i)
        (inhabit_int i)
    ; fresh (b) 
        (Info.leaf !!"bool" === arg_desc)
        (r === bool b)
        (inhabit_bool b)
    ; fresh (c th el)
        (if_ c th el === r)
        (inhabit_expr inhabit_bool (Info.leaf !!"bool") c)
        (inhabit_expr inh_arg arg_desc th)
        (inhabit_expr inh_arg arg_desc el)
    ]

(*let (_:int) = inhabit_expr*)
let inhabit_free r = (r===r)

(* int expr *)
let _f () = 
  run one (inhabit_expr inhabit_int (Info.leaf !!"int") )
    (fun r -> r#reify GExpr.reify)
  |> OCanren.Stream.take ~n:(10)
  |> (
       List.iteri (fun i x -> 
         Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
       ) 
      )
  ;
  Format.printf "\n%!"

(* bool expr *)
let _bool () = 
  run one (inhabit_expr inhabit_int (Info.leaf !!"bool") )
    (fun r -> r#reify GExpr.reify)
  |> OCanren.Stream.take ~n:(20)
  |> (
       List.iteri (fun i x -> 
         Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
       ) 
      )
  ;
  Format.printf "\n%!"

(* string expr hangs *)
let _hangs () = 
  run one (inhabit_expr inhabit_int (Info.leaf !!"string") )
    (fun r -> r#reify GExpr.reify)
  |> OCanren.Stream.take ~n:(20)
  |> (
       List.iteri (fun i x -> 
         Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
       ) 
      )
  ;
  Format.printf "\n%!"

(* 'a expr *)
let _fresh () = 
  run one (fun r -> fresh (x) (inhabit_expr inhabit_int x r))
    (fun r -> r#reify GExpr.reify)
  |> OCanren.Stream.take ~n:(20)
  |> (
       List.iteri (fun i x -> 
         Format.printf "%d:\t%a\n%!" i GT.(fmt GExpr.logic) x
       ) 
      )
  ;
  Format.printf "\n%!"

module Test2 = struct 
  type 'a choice = 
    | Int  : 'a -> int choice
    | Bool : 'a -> bool choice
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
    |> OCanren.Stream.take ~n:(-1)
    |> (
         List.iteri (fun i x -> 
           Format.printf "%d:\t%a\n%!" i GT.(fmt GChoice.logic @@ (fmt OCanren.logic @@ fmt int)) x
         ) 
        )
    ;
    Format.printf "\n%!"
      
  (* int choice *)
  let () = 
    run one (fun r -> inhabit_choice inhabit_int Info.int r)
      (fun r -> r#reify (GChoice.reify OCanren.reify))
    |> OCanren.Stream.take ~n:(-1)
    |> (
         List.iteri (fun i x -> 
           Format.printf "%d:\t%a\n%!" i GT.(fmt GChoice.logic @@ (fmt OCanren.logic @@ fmt int)) x
         ) 
        )
    ;
    Format.printf "\n%!"

  (* bool choice *)
  let () = 
    run one (fun r -> inhabit_choice inhabit_bool Info.bool r)
      (fun r -> r#reify (GChoice.reify OCanren.reify))
    |> OCanren.Stream.take ~n:(-1)
    |> (
         List.iteri (fun i x -> 
           Format.printf "%d:\t%a\n%!" i GT.(fmt GChoice.logic @@ (fmt OCanren.logic @@ fmt bool)) x
         ) 
        )
    ;
    Format.printf "\n%!"
end 
