open Unn_pre
module Trie = Lazy_trie


module type S  = sig
  type t
  type path = N.ground list


  val empty : t
  val add : t -> path -> TagSet.t -> t
  val is_set: t -> path -> bool
  val remove: t -> path -> t
  val find_exn: t -> path -> TagSet.t
  val minimize: t -> t

  val pp: Format.formatter -> t -> unit
end

include (struct

  type t = (Unn_pre.N.ground, TagSet.t) Trie.t
  type path = N.ground list

  let empty = Trie.empty
  let add (tr: t) p v = Trie.set tr p v
  (*
  let add_full_path tr p =
    List.fold_left (fun (trie, prefix) x ->
       let nextp = prefix @ [x] in
       (add trie nextp, nextp)
    )
    (add tr [],[]) p*)

  let find_exn = Trie.find
  let remove = Trie.sub

  let is_set tr p =
    try let _ = find_exn tr p in true
    with Not_found -> false

  let remove = Trie.sub
  let minimize =
    Trie.map_filter_values (fun set ->
      if TagSet.cardinal set > 1 then Some set else None
    )

  let pp fmt t =
    t |> Trie.iter (fun k set ->
      Format.fprintf fmt "\tS";
      Stdlib.List.iter (fun n -> Format.fprintf fmt "[%a]" (GT.fmt GT.int) (Unn_pre.N.to_int n)) k;
      Format.fprintf fmt " -> %a\n%!"
        (GT.fmt GT.list @@ (fun fmt tag ->
          let n = Tag.to_int tag in
          Format.fprintf fmt "%d=%s" n (Tag.string_of_tag_exn tag)
        ))
        (TagSet.elements set);
    )

end : S)


let build (clauses: Clauses.pre_ground) typs0 : t =
  let rec f acc typs cur_path (pattern: Pattern.ground) =
    let open Pattern in
    match pattern with
    | WildCard -> acc
    | PConstr (cname, xs) ->
        let acc = add acc cur_path (Typs.get_names typs) in
        let arg_typs = Typs.assoc_exn typs cname in
        (*
        Format.printf "%d typs: %s\n%!"
          (ground_list_length arg_typs)
          ((GT.show OCanren.Std.List.ground) (GT.show Typs.ground) arg_typs);
        Format.printf "%d pats: %s\n%!"
          (ground_list_length xs)
          ((GT.show OCanren.Std.List.ground) Pattern.show xs);
          *)
        ground_list_fold2i_exn (fun acc i arg argtyp ->
          let next_path = cur_path @ [ N.of_int i ] in
          f acc argtyp next_path arg
        ) acc xs arg_typs
  in
  List.fold_left
    (fun acc (p,_) -> f acc typs0 [] p)
    empty
    clauses
