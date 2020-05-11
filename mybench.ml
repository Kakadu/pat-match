module SMap = Map.Make(String)

module IMap = Map.Make(struct type t = int let compare = (compare: int -> int -> int) end)

type test_key = GT.string * GT.int GT.option * GT.int [@@deriving gt ~options:{compare}]
module TMap = Map.Make(struct
  type t = test_key
  let compare a b =
    match GT.compare test_key a b with
    | GT.EQ -> 0
    | GT.LT -> -1
    | GT.GT -> 1
end)
type test_data = Mtime.Span.t IMap.t TMap.t
let make_key a b c : test_key = (a,b,c)

type cfg =
  { mutable is_enabled: bool
  ; mutable cur_key: test_key

  ; mutable data: test_data
(*  ; mutable data_requested_count : int SMap.t*)
  ; mutable csv_filename: string
  }

let cfg =
  { is_enabled = false
  ; cur_key = ("",None,-1)
  ; data = TMap.empty
(*  ; data_requested_count = TMap.empty*)
  ; csv_filename = "/home/kakadu/asp/ocanren-ICFP2020/papers/MiniKanren-2020/matching/bench.csv"
  }

let enable ~on =
  cfg.is_enabled <- on;
  Format.printf "Benchmarking is on=%b\n%!" on

let set_start_info s ~n prunes =
  let k = make_key s prunes n in
  cfg.cur_key <- k;
  cfg.data <- TMap.add k IMap.empty cfg.data

let clear_startistics () = ()

let add_test_data idx span =
  let map1 = TMap.find cfg.cur_key cfg.data in
  let map2 = IMap.add idx span map1 in
  cfg.data <- TMap.add cfg.cur_key map2 cfg.data

(* ************************************************************************ *)
let when_enabled ~fail ok =
  if cfg.is_enabled then ok () else fail ()

let repeat f =
  when_enabled
    ~fail:f
    (fun () ->
      (* warmup *)
      f ();

    )

let got_answer span ~idx =
(*  assert false;*)
  Format.printf "got answer %d\n%!" idx;
  add_test_data idx span;
  ()

let finish () =
  when_enabled ~fail:(fun  () -> ())
    (fun () ->
      enable ~on:false;
      print_endline "printing results not implemented";

      let ch = open_out cfg.csv_filename in
      let ppf = Format.formatter_of_out_channel ch in
      Format.fprintf ppf "Name,First answer time, Answers requested, Answers found, All answers time,Pruning\n%!";
      cfg.data |> TMap.iter (fun (testname,prunes,answers_requested) v ->
        let answer1_str =
          let span = IMap.find 0 v in
          if Mtime.Span.to_ms span < 1000.
          then Printf.sprintf "%dms" (int_of_float @@ Mtime.Span.to_ms span)
          else Printf.sprintf "%30fs" (Mtime.Span.to_s span)
        in
        let answers_requested =
          if answers_requested<0 then "all" else string_of_int answers_requested
        in
        let prunes_info =
          match prunes with
          | None -> "always"
          | Some n -> Printf.sprintf "%d" n
        in
        let found_anwsers_count = IMap.cardinal v in
        let sum =
          let s = IMap.fold (fun _ v acc -> Mtime.Span.add acc v) v Mtime.Span.zero  in
          Format.asprintf "%3.1fms" (Mtime.Span.to_ms s)
        in
        Format.fprintf ppf "%s,%s,%s,%s,%d,%s\n%!"
          testname
          prunes_info
          answers_requested
          answer1_str
          found_anwsers_count
          sum
          ;
      );
      Format.pp_print_flush ppf ();
      close_out ch;
      let (_:int) = Sys.command @@ Printf.sprintf "cat '%s'" cfg.csv_filename in
      ()
    )
