val enable : on:bool -> unit
val when_enabled : fail:(unit -> 'a) -> (unit -> 'a) -> 'a

val set_start_info :
  string -> n:int -> int option -> clauses:string -> examples:int -> unit

val repeat : (unit -> unit) -> unit
val add_answer : int -> size:int -> Mtime.span -> unit
val add_nomore : Mtime.span -> unit
val set_best_answer_size : int -> unit
val set_first_answer_size : int -> unit

(*val start: unit -> unit*)
val finish : unit -> unit
val pp_span : Format.formatter -> Mtime.span -> unit
