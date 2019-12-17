let height = 2
type e = E of string * e list

let rec show_e = function
  | E (name, xs) ->
      Printf.sprintf "%s [%s]" name (show_es xs)
and show_es ?(sep="; ") xs = show_xs ~sep show_e xs
and show_xs ?(sep="; ") fa xs =
  String.concat sep @@ List.map fa xs
(* 
let rec populate_lists length (orig: 'a list) : 'a list list =
  Printf.printf "populate_lists length=%d\n%!" length;
  let rec helper n =
    if n<1 then failwith (Printf.sprintf "populate_list: bad argument %d" n)
    else if n=1 then List.map (fun h -> [h]) prev
    else
      let prevs : e list list = helper (n-1) in
      Printf.printf "prevs: { %s }\n" (String.concat ", " @@ List.map  (show_xs show_e) prevs);
      List.iter (fun xs -> assert (length = (List.length xs))) prevs;
      let hack = List.map (fun tl -> List.map (fun h -> tl) orig) prevs in
      let ans =
        List.flatten @@ hack

      in
      Printf.printf "ans: { %s }\n" (String.concat ", " @@ List.map  (show_xs show_e) ans);
      ans
  in
  let ans = helper length in
  List.iter (fun xs -> assert (length = (List.length xs))) ans;
  ans *)

let rec populate_lists : int -> 'a list -> 'a list list = fun n init ->
  if n<1 then assert false
  else if n = 1 then List.map (fun h -> [h]) init
  else
    List.flatten @@ List.map (fun xs -> List.map (fun h -> h::xs) init) @@
    populate_lists (n-1) init


let arity_map = List.to_seq [ ("nil", 0); ("pair", 2) ]

let econstr s xs = E (s,xs)

let rec builder (prev: 'a list) curh : 'a list =
  if curh > height
  then prev
  else
    arity_map
    |> Seq.flat_map (fun (name,arity) ->
        if arity = 0 then Seq.return @@ econstr name []
        else
          List.to_seq @@
          List.map (fun xs -> econstr name @@  xs) @@
          populate_lists arity prev
    )
    |> List.of_seq

let x = builder [econstr "a" []; econstr "b" []] 1
