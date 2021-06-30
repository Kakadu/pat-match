let run (module M : Main_inputs.ARG0) =
  Format.printf "%s %d\n%!" __FILE__ __LINE__;
  let filename = "/tmp/pm.smt2" in
  let ch = open_out filename in
  let ppf = Format.formatter_of_out_channel ch in
  let println fmt = Format.kfprintf (fun ppf -> Format.fprintf ppf "\n%!") fmt in
  println ppf "(set-logic  UFDTLIA)";
  let () = close_out ch in
  let _ = Sys.command @@ Format.sprintf "cat %s" filename in
  let _ =
    Sys.command (Format.sprintf "cvc5 --lang=sygus2 --sygus-pbe %s" filename)
  in
  ()
