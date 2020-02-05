open OCanren

let inhabit_free r = (r===r)
let inhabit_int  r = (r === !!1)
let inhabit_bool r = conde [ r=== !!false; r === !!true ]

(* ********************************************************************** *)
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
  let complex1 name x = complex name (Std.List.(!<) x)
  let leaf name : inj = complex name (Std.List.nil())

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
