#use "topfind";;
#rectypes;;
#require "GT";;
#require "GT.ppx";;

type lambda =
    | Lambda of string * lambda
    | Var of string
    | Apply of lambda * lambda
    [@@deriving gt]

open Format;;
let ident ppf s = fprintf ppf "%s" s
let kwd ppf s = fprintf ppf "%s" s

let rec pr_exp0 ppf = function
  | Var s -> fprintf ppf "%a" ident s
  | lam -> fprintf ppf "@[<1>(%a)@]" pr_lambda lam
and pr_app ppf e =
  fprintf ppf "@[<2>%a@]" pr_other_applications e
and pr_other_applications ppf f =
  match f with
  | Apply (f, arg) -> fprintf ppf "%a@ %a" pr_app f pr_exp0 arg
  | f -> pr_exp0 ppf f
and pr_lambda ppf = function
  | Lambda (s, lam) ->
     fprintf ppf "@[<1>%a%a%a@ %a@]"
             kwd "\\" ident s kwd "." pr_lambda lam
  | e -> pr_app ppf e;;

let pr_lambda2 ppf =
  GT.transform lambda
    (fun fself -> object(self)
      method pr_exp0 ppf = function
        | Var s -> fprintf ppf "%a" ident s
        | lam -> fprintf ppf "@[<1>(%a)@]" fself lam
      method pr_app ppf e =
        fprintf ppf "@[<2>%a@]" self#pr_other_applications e
      method pr_other_applications ppf f =
        match f with
        | Apply (f, arg) -> fprintf ppf "%a@ %a" pr_app f pr_exp0 arg
        | f -> pr_exp0 ppf f

      method c_Var fmt e _  = pr_app ppf e
      method c_Lambda fmt _ s lam =
        fprintf ppf "@[<1>%a%a%a@ %a@]"
              kwd "\\" ident s kwd "." fself lam
      method c_Apply fmt e _ _ = pr_app ppf e
    end)
    ppf

let (%) x y = Apply (x,y)

let zed =
  let x = Var "x" in
  let f = Var "f" in
  let l = Lambda ("f", Lambda ("a", (f % (x % x)) % (Var "a"))) in
  (Lambda ("f", Lambda ("g", (l%l)%(Var "g"))))

(* ************ *)
type ir =
  | Lit of GT.int
  | Switch of (GT.string * ir) GT.list
  [@@deriving gt ~options:{fmt}]

let rec pr_ir fmt = function
  | Lit n -> Format.fprintf fmt "%d" n
  | Switch xs ->
      Format.fprintf fmt "@[<v>(@[match ... with @]";
      GT.foldl GT.list
        (fun () (t,ir) ->
          Format.fprintf fmt "@[ | %s -> %a@]@;" t pr_ir ir
        ) () xs;
      Format.fprintf fmt ")@]"

let pr_2 f =
  GT.transform ir
    (fun fself -> object
      method c_Lit fmt _ n = Format.fprintf fmt "%d " n
      method c_Switch fmt _ xs =
        Format.fprintf fmt "@[(@[<2>match ... with @]";
        GT.foldl GT.list (fun () (t, code) ->
          Format.fprintf fmt "@[ | %s -> %a@]@;"
            t
            fself code
        ) () xs;
(*        Format.fprintf fmt "@[ | _ -> %a@]" fself on_default;*)
        Format.fprintf fmt ")@]"
    end)
    f


let switch1 =
  Switch
    [ "true", Lit 1
    ; "true", Lit 1
    ; "true", Lit 1
    ; "false",
       (Switch
         [ "true", (Switch
         [ "true", Lit 1
         ; "false", (Switch
         [ "true", Lit 1
         ; "false", Lit 2
         ])
         ])

         ])
    ]


let () =
  Format.pp_set_margin Format.std_formatter 150;
  Format.pp_set_max_indent Format.std_formatter (Format.pp_get_margin Format.std_formatter () - 1)

let () =
  Format.printf "%a\n%!" pr_lambda zed;
  Format.printf "%a\n%!" pr_lambda (zed%zed%zed%zed);
  Format.printf "%a\n%!" pr_lambda2 (zed%zed%zed%zed)


let () =
  Format.printf "%a\n%!" pr_ir switch1;
  Format.printf "%a\n%!" pr_2 switch1
