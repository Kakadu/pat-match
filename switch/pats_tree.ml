open Unn_pre
module Trie = Lazy_trie

module type S  = sig
  type t
  type path = N.ground list


  val empty : t
  val add : t -> path -> TagSet.t -> t
  val is_set: t -> path -> bool
  val find_exn: t -> path -> TagSet.t
  val remove: t -> path -> t

  val pp: Format.formatter -> t -> unit
end

include (struct

  type t = (N.ground, TagSet.t) Trie.t
  type path = N.ground list

  let empty = Trie.empty
  let add tr p v = Trie.set tr p v
  (*
  let add_full_path tr p =
    List.fold_left (fun (trie, prefix) x ->
       let nextp = prefix @ [x] in
       (add trie nextp, nextp)
    )
    (add tr [],[]) p
  *)

  let find_exn = Trie.find

  let is_set tr p =
    try let _ = find_exn tr p in true
    with Not_found -> false

  let remove = Trie.sub

  let pp fmt t =
    t |> Trie.iter (fun k set ->
      Format.fprintf fmt "\tS";
      List.iter (fun n -> Format.fprintf fmt "[%a]" (GT.fmt GT.int) (Unn_pre.N.to_int n)) k;
      Format.fprintf fmt " -> %a\n%!"
        (GT.fmt GT.list @@ (fun fmt tag ->
          let n = N.to_int tag in
          Format.fprintf fmt "%d=%s" n (Tag.string_of_tag_exn tag)
        ))
        (TagSet.elements set);
    )

end : S)


let build (clauses: Clauses.pre_ground) typs0 =
  let rec f acc typs cur_path (pattern: Pattern.ground) =
    let open Pattern in
    match pattern with
    | WildCard -> acc
    | PConstr (cname, xs) ->
        let acc = add acc cur_path (Typs.get_names typs) in
        let arg_typs = Typs.assoc_exn typs cname in
        ground_list_fold2i_exn (fun acc i arg argtyp ->
          let next_path = cur_path @ [ N.of_int i ] in
          f acc argtyp next_path arg
        ) acc xs arg_typs
  in
  List.fold_left
    (fun acc (p,_) -> f acc typs0 [] p)
    empty
    clauses
