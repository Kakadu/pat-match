val inhabit_free : 'a OCanren.ilogic -> OCanren.goal
val inhabit_int : int OCanren.ilogic -> OCanren.goal
val inhabit_bool : bool OCanren.ilogic -> OCanren.goal

module Info : sig
  type nonrec ('string, 'xs) t = Complex of 'string * 'xs
  [@@deriving gt ~options:{ gmap; fmt }]

  type ground = (string, ground OCanren.Std.List.ground) t
  [@@deriving gt ~options:{ gmap; fmt }]

  type logic =
    (string OCanren.logic, logic OCanren.Std.List.logic) t OCanren.logic
  [@@deriving gt ~options:{ gmap; fmt }]

  val fmapt :
    ('a -> 'b) OCanren.Env.m ->
    ('c -> 'd) OCanren.Env.m ->
    ('a, 'c) t OCanren.Env.m ->
    ('b, 'd) t OCanren.Env.m

  val prj_exn :
    ( ((string OCanren.ilogic, 'a OCanren.Std.List.groundi) t OCanren.ilogic
       as
       'a),
      (string, ground OCanren.Std.List.ground) t )
    OCanren.Reifier.t

  val reify :
    ( ((string OCanren.ilogic, 'a OCanren.Std.List.groundi) t OCanren.ilogic
       as
       'a),
      (string OCanren.logic, logic OCanren.Std.List.logic) t OCanren.logic )
    OCanren.Reifier.t

  val complex : 'a -> 'b -> ('a, 'b) t OCanren.ilogic

  type injected =
    (string OCanren.ilogic, injected OCanren.Std.List.groundi) t OCanren.ilogic

  val complex1 : 'a -> 'b -> ('a, 'b OCanren.Std.List.groundi) t OCanren.ilogic
  val leaf : string OCanren.ilogic -> injected
  val int : injected
  val bool : injected

  val size3 :
    ( string OCanren.ilogic,
      ( string OCanren.ilogic,
        (string OCanren.ilogic, injected OCanren.Std.List.groundi) t
        OCanren.ilogic
        OCanren.Std.List.groundi )
      t
      OCanren.ilogic
      OCanren.Std.List.groundi )
    t
    OCanren.ilogic

  val test : 'a -> unit
end

module GPair = OCanren.Std.Pair

val inhabit_pair :
  ('a OCanren.ilogic -> OCanren.goal) ->
  ('c OCanren.ilogic -> OCanren.goal) ->
  ('a OCanren.ilogic, 'c OCanren.ilogic) OCanren.Std.Pair.groundi ->
  OCanren.goal

module Bools : sig
  val test : 'a -> unit
end

module List : sig
  type 'a t = 'a list = [] | ( :: ) of 'a * 'a list

  val length : 'a list -> int
  val compare_lengths : 'a list -> 'b list -> int
  val compare_length_with : 'a list -> int -> int
  val cons : 'a -> 'a list -> 'a list
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val nth : 'a list -> int -> 'a
  val nth_opt : 'a list -> int -> 'a option
  val rev : 'a list -> 'a list
  val init : int -> (int -> 'a) -> 'a list
  val append : 'a list -> 'a list -> 'a list
  val rev_append : 'a list -> 'a list -> 'a list
  val concat : 'a list list -> 'a list
  val flatten : 'a list list -> 'a list
  val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
  val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int
  val iter : ('a -> unit) -> 'a list -> unit
  val iteri : (int -> 'a -> unit) -> 'a list -> unit
  val map : ('a -> 'b) -> 'a list -> 'b list
  val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
  val rev_map : ('a -> 'b) -> 'a list -> 'b list
  val filter_map : ('a -> 'b option) -> 'a list -> 'b list
  val concat_map : ('a -> 'b list) -> 'a list -> 'b list
  val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val for_all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val mem : 'a -> 'a list -> bool
  val memq : 'a -> 'a list -> bool
  val find : ('a -> bool) -> 'a list -> 'a
  val find_opt : ('a -> bool) -> 'a list -> 'a option
  val find_map : ('a -> 'b option) -> 'a list -> 'b option
  val filter : ('a -> bool) -> 'a list -> 'a list
  val find_all : ('a -> bool) -> 'a list -> 'a list
  val filteri : (int -> 'a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val partition_map : ('a -> ('b, 'c) Either.t) -> 'a list -> 'b list * 'c list
  val assoc : 'a -> ('a * 'b) list -> 'b
  val assoc_opt : 'a -> ('a * 'b) list -> 'b option
  val assq : 'a -> ('a * 'b) list -> 'b
  val assq_opt : 'a -> ('a * 'b) list -> 'b option
  val mem_assoc : 'a -> ('a * 'b) list -> bool
  val mem_assq : 'a -> ('a * 'b) list -> bool
  val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
  val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list
  val split : ('a * 'b) list -> 'a list * 'b list
  val combine : 'a list -> 'b list -> ('a * 'b) list
  val sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val sort_uniq : ('a -> 'a -> int) -> 'a list -> 'a list
  val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
  val to_seq : 'a list -> 'a Seq.t
  val of_seq : 'a Seq.t -> 'a list
  val max : 'a t -> 'a
  val take : int -> 'a t -> 'a t
end

val show_local_time : unit -> unit
