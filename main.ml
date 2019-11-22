let () =
  print_endline "hello world"


(*
 `s` -- scrutinee
 `ps` -- list of patterns
 `candidates s ps` -- gives valuable scrutinees for patters
 `n` -- one of the RHSes of pattern matching
 `〚ps〛` -- patterns compiled to IR
 `evalPM p s n` -- interpreter for pmatch language: takes
    - [p] -- list of pairs pattern * RHS
    - [s] -- scrutinee
    - [n] -- expected RHS
  `〚ps〛` -- patterns compiled to IR


  `ps` -- always ground
  `pswitch` -- always ground
  `n` -- always ground

  fresh (s)
    candidates s ps &&& evalPM pswitch s n &&& evalIR 〚ps〛 s n
*)

module Pattern = struct
  type 'xs t  = PWildCard
              | PConstr of 'xs
  include OCanren.Fmap(struct
    type nonrec 'a t = 'a t
    let fmap f = function
      | PWildCard -> PWildCard
      | PConstr xs -> PConstr (f xs)
  end)

  type ground = ground OCanren.Std.List.ground t
  type logic  = logic OCanren.Std.List.logic t OCanren.logic

  let rec pp_ground fmt : ground -> unit = function
    | PWildCard -> Format.fprintf fmt "_"
    | PConstr xs -> GT.fmt OCanren.Std.List.ground pp_ground fmt xs

  let rec pp_logic : Format.formatter -> logic -> unit = fun fmt p ->
    GT.fmt OCanren.logic
      (fun fmt -> function
        | PWildCard -> Format.fprintf fmt "_"
        | PConstr xs -> GT.fmt OCanren.Std.List.logic pp_logic fmt xs
      )
      fmt p

end

open OCanren
let addo x y =
  Fresh.one (fun z ->
    (x === y)
  )

let oooo x y =
  fresh (z)
    (x === y)



(*
match scru with
| ([], _) -> 1
| (_, []) -> 2
| (_::_, _) -> 3
*)
