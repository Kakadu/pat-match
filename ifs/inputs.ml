open OCanren

module Type = struct
  [%%distrib
  type nonrec 'a t = T of 'a [@@deriving gt ~plugins:{ gmap }]

  (* typinfo = list of pair of tags and typinfo *)
  type ground = (GT.int, ground) Std.Pair.ground Std.List.ground t]
end

module TypsHighlevel = struct
  type constr_name = string
  type accessor_name = string
  type typ_name = string

  (* type t0 = Nonrec of adt | Mu of string * adt | Named of string *)

  type arg = accessor_name option * typ_name
  type adt = (constr_name * arg list) list
  type type_def = Nonrec of adt | Mu of string * adt

  let arg : ?acc:accessor_name -> typ_name -> arg = fun ?acc name -> (acc, name)

  type env = (string * type_def) list
  type t = env * adt

  let next_name =
    let last_name = ref 0 in
    fun () ->
      incr last_name;
      (Format.sprintf "typ%d" !last_name : typ_name)

  let list el =
    let n = next_name () in
    Mu (n, [ ("nil", []); ("cons", [ (Some "hd", el); (Some "tl", n) ]) ])

  let pair a b = Nonrec [ ("Pair", [ (None, a); (None, b) ]) ]
  let int = Nonrec [ ("42", []) ]
  (*
  let unfold : _ -> t -> Type.ground =
    let rec helper env depth typname =
      if depth <= 0 then Type.T []
      else
        match List.assoc typname env with
        | exception Not_found -> assert false
        | Nonrec rhs -> on_alg env depth rhs
        | Mu (name, rhs) ->
            let env = (name, Nonrec rhs) :: env in
            on_alg env depth rhs
    (* | Named n -> (
       match List.assoc n env with
       | exception Not_found -> assert false
       | typ -> helper env depth typ ) *)
    and on_alg env depth (rhs : adt) =
      T
        (List.map
           (fun (name, args) ->
             ( name,
               List.map
                 (fun (_, typname) -> helper env (depth - 1) typname)
                 args ))
           rhs)
    in
    fun depth (env, adt) -> on_alg env depth adt *)
end
