open Unn_pre
module Trie = Lazy_trie


module type S  = sig
  type t
  type path = N.ground list


  val empty : t
  val add : t -> path -> t
  val is_set: t -> path -> bool

  val pp: Format.formatter -> t -> unit
end

include (struct

  type t = (Unn_pre.N.ground, unit) Trie.t
  type path = N.ground list

  let empty = Trie.empty
  let add tr p = Trie.set tr p (())
  let add_full_path tr p =
    List.fold_left (fun (trie, prefix) x ->
       let nextp = prefix @ [x] in
       (add trie nextp, nextp)
    )
    (add tr [],[]) p

  let is_set tr p =
    try let _ = Trie.find tr p in true
    with Not_found -> false

  let pp fmt t =
    t |> Trie.iter (fun k () ->
      Format.fprintf fmt "\tS";
      List.iter (fun n -> Format.fprintf fmt "[%a]" (GT.fmt GT.int) (Unn_pre.N.to_int n)) k;
      Format.fprintf fmt "\n%!";
    )

end : S)


let build (clauses: Clauses.pre_ground) =
  (*let rec to_list = function
    | Scru -> []
    | Field (n, xs) -> (to_list xs) @ [n]
  in*)
  let rec f acc cur_path (pattern: Pattern.ground) =
    let open Pattern in
    match pattern with
    | WildCard -> acc
    | PConstr (_, xs) ->
        let acc = add acc cur_path in
        ground_list_foldi (fun acc i item ->
          let next_path = cur_path @ [ N.of_int i ] in
          f acc next_path item
        ) acc xs
  in
  List.fold_left
    (fun acc (p,_) -> f acc [] p)
    empty
    clauses
