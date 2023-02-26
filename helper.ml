open OCanren
open Printf

let inhabit_free r = (r===r)
let inhabit_int  r = (r === !!1)
let inhabit_bool r = conde [ r=== !!false; r === !!true ]

(* ********************************************************************** *)
module Info = struct
  [%%ocanren
  type nonrec ('string, 'xs) t = Complex of 'string * 'xs
    [@@deriving gt ~options:{gmap; fmt}]

  type ground = (GT.string, ground Std.List.ground) t
  ]
  (* module F = Fmap2(struct
    type ('a, 'b) t = ('a, 'b) ginfo
    let fmap p q x = (GT.gmap ginfo) p q x
  end) *)

  (* type ground = (GT.string,              ground Std.List.ground) ginfo *)
  (* type logic  = (GT.string OCanren.logic, logic Std.List.logic) ginfo OCanren.logic *)
    (* [@@deriving gt ~options:{fmt}] *)

  (* type inj = (ground, logic) OCanren.injected *)

  (* let rec reify env (x: inj) : logic = F.reify OCanren.reify (Std.List.reify reify) env x *)

  let complex name xs = inj @@ (Complex (name,xs))
  let complex1 name x = complex name (Std.List.(!<) x)
  let leaf name : injected = complex name (Std.List.nil())

  let int = leaf !!"int"
  let bool = leaf !!"bool"

  let size3 = complex1 !!"s" @@ complex1 !!"s" @@ complex1 !!"s" @@ leaf !!"z"

  let test _ =
    run one (fun q -> (q === leaf !!"int"))
      (fun r -> r#reify reify)
      |> OCanren.Stream.take ~n:(-1)
      |> GT.(fmt list) GT.(fmt logic) Format.std_formatter;
    Format.printf "\n%!"
end

module GPair = OCanren.Std.Pair

let inhabit_pair : (*'a 'b 'c 'd.*)
    ('a OCanren.ilogic -> goal) ->
    ('c OCanren.ilogic -> goal) ->
    (*left_desc: Info.inj ->
    right_desc: Info.inj ->*)
    (('a * 'c) OCanren.ilogic) ->
    goal
  = fun inh_left inh_right r ->
  conde
    [ fresh (l r)
        (r === Std.pair l r)
        (inh_left l)
        (inh_right r)
    ]

module Bools = struct
  let test _ =
    run one (fun q -> (q =/= !!true) &&& (q =/= !!false))
      (fun r -> r#reify reify)
      |> OCanren.Stream.hd
      |> (fun bl -> printf "%s\n%!" (GT.(show OCanren.logic @@ show bool) bl));
    Format.printf "\n%!"
end

module List = struct
  include List
  let max xs =
    match xs with
    | [] -> failwith "bad argument of List.max"
    | x::xs -> List.fold_left max x xs


  let rec take n xs =
    if n = 0 then [] else
    match xs with
    | x::xs ->  x :: (take (n-1) xs)
    | [] -> failwith "bad argument"

end

let show_local_time () =
  let tm = Unix.(localtime @@ time ()) in
  Format.printf "starting time: %02d:%02d:%02d\n%!" tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
