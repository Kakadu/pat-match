module Cfg = Configurator.V1

(*** discovering ***)
let discover lib ~filename cfg =
  let path =
    String.trim @@ Cfg.Process.run_capture_exn cfg "ocamlfind" [ "query"; lib ]
  in
  let _ = Sys.command (Format.sprintf "echo '%s' > %s" path filename) in
  ()

let discover_GT = discover "GT" ~filename:"path-GT.cfg"
let discover_OCanren = discover "OCanren" ~filename:"path-OCanren.cfg"
let discover_Maybe = discover "noCanren.Maybe" ~filename:"path-Maybe.cfg"

(*** main ***)

let () =
  Cfg.main ~name:"lib" (fun cfg ->
      discover_GT cfg;
      discover_OCanren cfg;
      (* discover_Maybe cfg; *)
      ())
