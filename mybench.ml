module Time = struct
  let now () = Unix.(localtime @@ time() )
  let months = [| "Jan"; "Feb"; "Mar"; "Apr"; "May"; "Jun"; "Jul"; "Aug"; "Sep"; "Oct"; "Nov"; "Dec" |]
  let str_of_month n =
    if n>=0 && n<=12 then months.(n)
    else failwith "Wrong argument of str_of_month"
  let to_string {Unix.tm_sec; Unix.tm_mon; Unix.tm_min; Unix.tm_hour; Unix.tm_mday; Unix.tm_year; _ } =
    Printf.sprintf "%02d %s, %d %02d:%02d:%02d"
            tm_mday (str_of_month tm_mon) (1900+tm_year) tm_hour tm_min tm_sec
end

module SMap = Map.Make(String)

module IMap = Map.Make(struct type t = int let compare = (compare: int -> int -> int) end)

type test_key =
  { tk_name : GT.string
  ; tk_prunes : GT.int GT.option
  ; tk_answers : GT.int
  ; tk_clauses : GT.string
  }
  [@@deriving gt ~options:{compare}]

module TMap = Map.Make(struct
  type t = test_key
  let compare a b =
    match GT.compare test_key a b with
    | GT.EQ -> 0
    | GT.LT -> -1
    | GT.GT -> 1
end)
type test_data = Mtime.Span.t IMap.t TMap.t
let make_key tk_name tk_prunes tk_answers tk_clauses =
  { tk_name; tk_prunes; tk_answers; tk_clauses }

type cfg =
  { mutable is_enabled: bool
  ; mutable cur_key: test_key
  ; mutable data: test_data
  ; mutable csv_filename: string
  ; mutable list_filename: string
  }

let cfg =
  { is_enabled = false
  ; cur_key = (make_key "" None (-1) "")
  ; data = TMap.empty
  ; csv_filename = "/home/kakadu/asp/ocanren-ICFP2020/papers/MiniKanren-2020/matching/bench.csv"
  ; list_filename = "/home/kakadu/asp/ocanren-ICFP2020/papers/MiniKanren-2020/matching/lst.tex"
  }

let enable ~on =
  cfg.is_enabled <- on;
  Format.printf "Benchmarking is on=%b\n%!" on

let set_start_info s ~n prunes ~clauses =
  let k = make_key s prunes n clauses in
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
(*      Format.fprintf ppf "# Autogenerated %s\n%!" Time.(now () |> to_string);*)
      Format.fprintf ppf "Name,Pruning, Answers requested,First answer time, Answers found, All answers time\n%!";

      let listings_ch = open_out cfg.list_filename in
      Printf.fprintf listings_ch "%%%% Autogenerated %s\n\n%!" Time.(now () |> to_string);

      cfg.data |> TMap.iter (fun ({ tk_name; tk_prunes; tk_answers=answers_requested } as tk) v ->
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
          match tk_prunes with
          | None -> "always"
          | Some n -> Printf.sprintf "%d" n
        in
        let found_anwsers_count = IMap.cardinal v in
        let sum =
          let s = IMap.fold (fun _ v acc -> Mtime.Span.add acc v) v Mtime.Span.zero  in
          Format.asprintf "%3.1fms" (Mtime.Span.to_ms s)
        in
        Format.fprintf ppf "%s,%s,%s,%s,%d,%s\n%!"
          tk.tk_name
          prunes_info
          answers_requested
          answer1_str
          found_anwsers_count
          sum;

        Printf.fprintf listings_ch "\\begin{lstlisting}\n(* %s *)\n%s\\end{lstlisting}\n\n" tk.tk_name tk.tk_clauses;
      );
      Format.pp_print_flush ppf ();
      close_out ch;
      close_out listings_ch;
      let (_:int) = Sys.command @@ Printf.sprintf "cat '%s'" cfg.csv_filename in
      ()
    )
