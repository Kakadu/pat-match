let failwithf fmt = Format.kasprintf failwith fmt

type test_key = {
  tk_name : GT.string;
  tk_prunes : GT.int GT.option;
  tk_answers : GT.int;
  tk_clauses : GT.string;
  tk_ex_count : GT.int;
}
[@@deriving gt ~options:{ compare }]

let make_key tk_name tk_prunes tk_answers tk_clauses tk_ex_count =
  { tk_name; tk_prunes; tk_answers; tk_clauses; tk_ex_count }

module IMap = Map.Make (Int)

module TMap = Map.Make (struct
  type t = test_key

  let compare a b =
    match GT.compare test_key a b with GT.EQ -> 0 | GT.LT -> -1 | GT.GT -> 1
end)

module SMap = Map.Make (String)

module Runs = struct
  open Mtime

  type t = Span.t list

  let extend t x = x :: t
  let count = List.length
  let make span = [ span ]
  let empty = []

  let avg_ms iterations_count t =
    assert (count t = iterations_count);
    let s =
      List.fold_left
        (fun acc span -> acc +. (Mtime.Span.to_float_ns span /. 1e6))
        0.0 t
    in
    s /. float_of_int (count t)

  let avg_s iterations_count t =
    assert (count t = iterations_count);
    avg_ms iterations_count t /. 1000.0

  let sum_span iterations_count xs =
    assert (count xs = iterations_count);
    List.fold_left Mtime.Span.add Mtime.Span.zero xs
end

type 'a experiment = { answers : 'a IMap.t; no_more : 'a }

type cfg = {
  mutable is_enabled : bool;
  mutable cur_key : test_key;
  (* It should be a map
    test -> (int | postproof) Map -> Runs.t *)
  mutable data : Runs.t experiment TMap.t;
  mutable csv_filename : string;
  mutable list_filename : string;
  mutable iterations_count : int;
}

let cfg =
  {
    is_enabled = false;
    cur_key = make_key "" None (-1) "" 0;
    data = TMap.empty;
    csv_filename = "bench.csv";
    list_filename = "lst.tex";
    iterations_count = 10;
  }

let () =
  cfg.iterations_count <-
    (match Sys.getenv_opt "PAT_MATCH_REPEAT" with
    | None -> cfg.iterations_count
    | Some s -> ( try int_of_string s with Failure _ -> cfg.iterations_count))

module Time = struct
  let now () = Unix.(localtime @@ time ())

  let months =
    [|
      "Jan";
      "Feb";
      "Mar";
      "Apr";
      "May";
      "Jun";
      "Jul";
      "Aug";
      "Sep";
      "Oct";
      "Nov";
      "Dec";
    |]

  let str_of_month n =
    if n >= 0 && n <= 12 then months.(n)
    else failwith "Wrong argument of str_of_month"

  let to_string
      {
        Unix.tm_sec;
        Unix.tm_mon;
        Unix.tm_min;
        Unix.tm_hour;
        Unix.tm_mday;
        Unix.tm_year;
        _;
      } =
    Printf.sprintf "%02d %s, %d %02d:%02d:%02d" tm_mday (str_of_month tm_mon)
      (1900 + tm_year) tm_hour tm_min tm_sec
end

let enable ~on =
  cfg.is_enabled <- on;
  Format.printf "Benchmarking is on=%b\n%!" on

let latex_name name prunes =
  let suffix =
    match prunes with
    | None -> ""
    | Some 10 -> "pX"
    | Some 100 -> "pL"
    | Some 777 -> "pLLL"
    | _ ->
        failwithf "prunes a not known: %a"
          Format.(pp_print_option pp_print_int)
          prunes
  in
  match name with
  | "A|B|C" -> "ABC"
  | "BIG (no cons -- use WCs)" -> "BIG"
  | "bool" -> "BOOL"
  | "bool*bool" -> "BoolII"
  | "bool*bool*bool (Maranget;page1)" -> "BoolIII" ^ suffix
  | "simple lists (from Maranget2008)" -> "ListI"
  | "simple nats (a la Maranget2008)" -> "NatI"
  | "two-nil lists (with cons)" -> "ListII"
  | "two-nil lists (with cons; simplified RHS)" -> "ListIII" ^ suffix
  | s -> failwithf "No latex name specified: %s" s

let set_start_info s ~n prunes ~clauses ~examples =
  (* Abort early *)
  let _ : string = latex_name s prunes in
  let k = make_key s prunes n clauses examples in
  cfg.cur_key <- k;
  cfg.data <- TMap.add k { answers = IMap.empty; no_more = Runs.empty } cfg.data

let clear_startistics () = ()

let add_span ~span ~iteration idx map =
  Format.printf "add_span for idx = %d\n%!" idx;
  try
    let r = IMap.find idx map in
    IMap.add idx (Runs.extend r span) map
  with Not_found -> IMap.add idx (Runs.make span) map

let add_anwer ~iteration idx span =
  let ex = TMap.find cfg.cur_key cfg.data in
  let map2 = add_span ~iteration idx ~span ex.answers in
  cfg.data <- TMap.add cfg.cur_key { ex with answers = map2 } cfg.data

let add_nomore ~iteration span = assert false

(* ************************************************************************ *)
let when_enabled ~fail ok = if cfg.is_enabled then ok () else fail ()

let repeat f =
  when_enabled ~fail:f (fun () ->
      (* warmup *)
      (*      f ();*)
      for i = 1 to cfg.iterations_count do
        Printf.printf "going iteration %d/%d\n%!" i cfg.iterations_count;
        Gc.full_major ();
        Gc.compact ();
        f ();
        Gc.full_major ();
        Gc.compact ()
      done)

let pp_span ppf span =
  let ms = Mtime.Span.to_float_ns span /. 1e6 in
  if ms > 10000. then Format.fprintf ppf "%10.0fs\n%!" (ms /. 1e3)
  else Format.fprintf ppf "%10.0fms\n%!" ms

let got_answer span ~idx =
  Format.printf "got answer %d, span = %a\n%!" idx pp_span span;
  add_test_data idx span;
  ()

let finish () =
  let calc tk_name tk_prunes answers_requested v =
    let answer1_str =
      let runs = IMap.find 0 v in
      let ms = Runs.avg_ms cfg.iterations_count runs in
      if ms < 1000. then Printf.sprintf "%dms 3" (int_of_float ms)
      else Printf.sprintf "%30fs" (Runs.avg_s cfg.iterations_count runs)
    in
    let answers_requested =
      if answers_requested < 0 then "all" else string_of_int answers_requested
    in
    let prunes_info =
      match tk_prunes with None -> "always" | Some n -> Printf.sprintf "%d" n
    in
    let found_anwsers_count = IMap.cardinal v in
    let sum =
      let s =
        IMap.fold
          (fun _ v acc -> acc +. Runs.avg_ms cfg.iterations_count v)
          v 0.0
      in
      Format.asprintf "%3.1fms" s
    in
    (prunes_info, answer1_str, found_anwsers_count, answers_requested, sum)
  in
  let make_csv () =
    let ch = open_out cfg.csv_filename in
    let ppf = Format.formatter_of_out_channel ch in
    Format.fprintf ppf
      "Name,Pruning, Answers requested,Examples generated,First answer time, \
       Answers found, All answers time\n\
       %!";

    TMap.iter
      (fun ({ tk_name; tk_prunes; tk_answers = answers_requested } as tk) v ->
        Format.printf "Generating table for test `%s`\n%!" tk_name;
        let ( prunes_info,
              answer1_str,
              found_anwsers_count,
              answers_requested,
              sum ) =
          calc tk_name tk_prunes answers_requested v
        in
        Format.fprintf ppf "%s,%s,%s,%d,%s,%d,%s\n%!" tk.tk_name prunes_info
          answers_requested tk.tk_ex_count answer1_str found_anwsers_count sum)
      cfg.data;
    Format.pp_print_flush ppf ();
    close_out ch
  in

  let make_tex () =
    let listings_ch = open_out cfg.list_filename in
    Printf.fprintf listings_ch "%%%% Autogenerated %s\n\n%!"
      Time.(now () |> to_string);
    let ppf = Format.std_formatter in
    let printfn fmt = Format.kasprintf (Format.fprintf ppf "%s\n%!") fmt in
    Format.printf "TMap.cardinal = %d\n%!" (TMap.cardinal cfg.data);
    TMap.iter
      (fun ({ tk_name; tk_prunes; tk_answers = answers_requested } as tk) v ->
        Format.printf "IMap.cardinal = %d\n%!" (IMap.cardinal v);
        Format.printf "Generating table for test `%s`\n%!" tk_name;
        let ( prunes_info,
              answer1_str,
              found_anwsers_count,
              answers_requested,
              sum ) =
          calc tk_name tk_prunes answers_requested v
        in
        let lname = latex_name tk_name tk_prunes in
        printfn "\\def\\m%ssamples{%d}" lname tk.tk_ex_count;
        printfn "\\def\\m%s%s{%d}" lname "answers" found_anwsers_count;
        printfn "\\def\\m%s%s{%d}" lname "firstSize" tk.tk_ex_count;
        printfn "\\def\\m%s%s{%d}" lname "firstTime" tk.tk_ex_count;
        printfn "\\def\\m%s%s{%d}" lname "optSize" tk.tk_ex_count;
        printfn "\\def\\m%s%s{%d}" lname "optTime" tk.tk_ex_count;
        printfn "\\def\\m%s%s{%d}" lname "total" tk.tk_ex_count;
        Format.pp_print_flush ppf ();
        Printf.fprintf listings_ch
          "\\begin{lstlisting}\n(* %s *)\n%s\\end{lstlisting}\n\n" tk.tk_name
          tk.tk_clauses)
      cfg.data;
    close_out listings_ch
  in
  when_enabled
    ~fail:(fun () -> ())
    (fun () ->
      enable ~on:false;

      TMap.iter
        (fun { tk_name } v ->
          (* Format.printf "Generating table for test `%s`\n%!" tk_name; *)
          IMap.iter
            (fun k v ->
              let vlen = List.length v in
              if vlen = cfg.iterations_count then ()
              else failwithf "iteration count mismatch. length = %d" vlen)
            v;
          if IMap.cardinal v = 0 then
            failwith "We should not include tests with no answers")
        cfg.data;

      make_csv ();
      make_tex ();

      let (_ : int) =
        Sys.command @@ Printf.sprintf "cat '%s'" cfg.csv_filename
      in
      ())
