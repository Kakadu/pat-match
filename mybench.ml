let failwithf fmt = Format.kasprintf failwith fmt

let pp_span ppf span =
  let ms = Mtime.Span.to_float_ns span /. 1e6 in
  if ms > 10000. then Format.fprintf ppf "%10.0fs\n%!" (ms /. 1e3)
  else Format.fprintf ppf "%10.0fms\n%!" ms

let rec to_roman = function
  | 1 -> "I"
  | 2 -> "II"
  | 3 -> "III"
  | 4 -> "IV"
  | 5 -> "V"
  | 6 -> "VI"
  | 7 -> "VII"
  | x -> failwithf "%s: not implemented %d" __FUNCTION__ x

let pp_float_time ppf timems =
  if timems < 1000. then Format.fprintf ppf "%10.1fms" timems
  else Format.fprintf ppf "%10.1fs" (timems /. 1000.0)

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

type avg = { min : float; avg : float; max : float }

module Runs = struct
  open Mtime

  type t = Span.t list

  let extend t x = x :: t
  let count = List.length
  let make span = [ span ]
  let empty = []
  let nth i xs = List.nth xs i

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

  (** Convert spans into ms and calculate statistics *)
  let statistics span =
    let ans =
      List.fold_left
        (fun acc v ->
          let v = Mtime.Span.to_float_ns v /. 1e6 in
          {
            min = Float.min acc.min v;
            max = Float.max acc.max v;
            avg = acc.avg +. v;
          })
        { min = Float.infinity; max = Float.neg_infinity; avg = 0.0 }
        span
    in
    { ans with avg = ans.avg /. float_of_int (List.length span) }
end

type 'a experiment = {
  mutable answers : (int * 'a) IMap.t;
  mutable no_more : 'a;
}

(* Return statistics in milliseconds of whole synthesis time *)
let get_stats2 iters : Runs.t experiment -> _ =
 fun e ->
  let min = ref Float.infinity in
  let sum = ref 0. in
  let max = ref Float.neg_infinity in
  for i = 0 to iters - 1 do
    let cur =
      IMap.fold
        (fun _ (_, v) acc -> Mtime.Span.add acc (Runs.nth i v))
        e.answers (Runs.nth i e.no_more)
      |> Mtime.Span.to_float_ns
    in
    sum := !sum +. cur;
    min := Float.min cur !min;
    max := Float.max cur !max
  done;
  {
    min = !min /. 1e6;
    avg = !sum /. 1e6 /. float_of_int iters;
    max = !max /. 1e6;
  }

let map_experiment f e =
  {
    no_more = f e.no_more;
    answers = IMap.map (fun (n, x) -> (n, f x)) e.answers;
  }

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

let add_answer idx ~size span =
  let ex = TMap.find cfg.cur_key cfg.data in
  ex.answers <-
    (match IMap.find idx ex.answers with
    | exception Not_found -> IMap.add idx (size, Runs.make span) ex.answers
    | size0, r ->
        assert (size = size0);
        IMap.add idx (size0, Runs.extend r span) ex.answers)

let add_nomore span =
  let ex = TMap.find cfg.cur_key cfg.data in
  ex.no_more <- Runs.extend ex.no_more span

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

let finish () =
  let calc tk_name tk_prunes answers_requested v =
    let _ : avg experiment = v in
    let answer1_str =
      let _, runs = IMap.find 0 v.answers in
      let ms = runs.avg in
      if ms < 1000. then Printf.sprintf "%dms 3" (int_of_float ms)
      else Printf.sprintf "%30fs" (ms /. 1000.0)
    in
    let answers_requested =
      if answers_requested < 0 then "all" else string_of_int answers_requested
    in
    let prunes_info =
      match tk_prunes with None -> "always" | Some n -> Printf.sprintf "%d" n
    in
    let found_anwsers_count = IMap.cardinal v.answers in
    let sum =
      let s =
        IMap.fold (fun _ (_, v) acc -> acc +. v.avg) v.answers v.no_more.avg
      in
      Format.asprintf "%3.1fms" s
    in
    (* TODO: maybe extract time of proving that no more answers *)
    (prunes_info, answer1_str, found_anwsers_count, answers_requested, sum)
  in
  let make_csv data =
    Out_channel.with_open_text cfg.csv_filename (fun ch ->
        let ppf = Format.formatter_of_out_channel ch in
        Format.fprintf ppf
          "Name,Pruning, Answers requested,Examples generated,First answer \
           time, Answers found, All answers time\n\
           %!";

        TMap.iter
          (fun ({ tk_name; tk_prunes; tk_answers = answers_requested } as tk) v
             ->
            let _ : avg experiment = v in
            Format.printf "%%Generating table for test `%s`\n%!" tk_name;
            let ( prunes_info,
                  answer1_str,
                  found_anwsers_count,
                  answers_requested,
                  sum ) =
              calc tk_name tk_prunes answers_requested v
            in
            Format.fprintf ppf "%s,%s,%s,%d,%s,%d,%s\n%!" tk.tk_name prunes_info
              answers_requested tk.tk_ex_count answer1_str found_anwsers_count
              sum)
          data;
        Format.pp_print_flush ppf ())
  in

  let make_tex () =
    Out_channel.with_open_text cfg.list_filename (fun listings_ch ->
        Printf.fprintf listings_ch "%%%% Autogenerated %s\n\n%!"
          Time.(now () |> to_string);
        let ppf = Format.std_formatter in
        let printfn fmt =
          Format.kasprintf
            (fun s ->
              Format.fprintf ppf "%s\n%!" s;
              Printf.fprintf listings_ch "%s\n" s)
            fmt
        in

        TMap.iter
          (fun ({ tk_name; tk_prunes; tk_answers = answers_requested } as tk) v
             ->
            let pp_error ppf { min; avg; max } =
              Format.fprintf ppf "-%2.0f\\%% +%2.0f\\%%"
                ((avg -. min) /. avg *. 100.)
                ((max -. avg) /. avg *. 100.)
            in

            let _ : Runs.t experiment = v in
            let vAvg : _ experiment = map_experiment Runs.statistics v in
            Format.printf "%%Generating table for test `%s`\n%!" tk_name;
            let ( prunes_info,
                  answer1_str,
                  found_anwsers_count,
                  answers_requested,
                  sum ) =
              calc tk_name tk_prunes answers_requested vAvg
            in
            let lname = latex_name tk_name tk_prunes in
            let stats2 = get_stats2 cfg.iterations_count v in
            printfn "\\def\\m%s%s{%d}" lname "samples" tk.tk_ex_count;
            printfn "\\def\\m%s%s{%d}" lname "answers" found_anwsers_count;
            printfn "\\def\\m%s%s{%a}" lname "totalAvg" pp_float_time stats2.avg;
            printfn "\\def\\m%s%s{%a}" lname "totalMin" pp_float_time stats2.min;
            printfn "\\def\\m%s%s{%a}" lname "totalMax" pp_float_time stats2.max;
            printfn "\\def\\m%s%s{%a}" lname "totalError" pp_error stats2;
            let () =
              IMap.iter
                (fun k (sz, { avg }) ->
                  printfn "\\def\\m%s%s%sTime{%a}" lname "Avg"
                    (to_roman (k + 1))
                    pp_float_time avg;
                  printfn "\\def\\m%s%s%sTime{%d}" lname "AnsSize"
                    (to_roman (k + 1))
                    sz)
                vAvg.answers;
              printfn "\\def\\m%s%s%sTime{%a}" lname "Avg" "NoMore"
                pp_float_time vAvg.no_more.avg
            in
            Format.pp_print_flush ppf ();
            Printf.fprintf listings_ch
              "\\begin{lstlisting}\n(* %s *)\n%s\\end{lstlisting}\n\n"
              tk.tk_name tk.tk_clauses)
          cfg.data)
  in
  when_enabled
    ~fail:(fun () -> ())
    (fun () ->
      enable ~on:false;

      TMap.iter
        (fun { tk_name } v ->
          (* Format.printf "Generating table for test `%s`\n%!" tk_name; *)
          let _ : _ experiment = v in
          IMap.iter
            (fun k (_, v) ->
              let vlen = List.length v in
              if vlen = cfg.iterations_count then ()
              else failwithf "iteration count mismatch. length = %d" vlen)
            v.answers;
          if IMap.cardinal v.answers = 0 then
            failwith "We should not include tests with no answers")
        cfg.data;
      let data = TMap.map (map_experiment Runs.statistics) cfg.data in
      make_csv data;
      make_tex ();

      let (_ : int) =
        Sys.command @@ Printf.sprintf "cat '%s'" cfg.csv_filename
      in
      ())
