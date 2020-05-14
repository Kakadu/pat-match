val enable: on:bool -> unit

val when_enabled: fail:(unit -> 'a) -> (unit -> 'a) -> 'a

val set_start_info: string -> n:int -> int option -> clauses:string -> unit

val repeat: (unit -> unit) -> unit

val got_answer: Mtime.Span.t -> idx:int -> unit

(*val start: unit -> unit*)
val finish: unit -> unit
