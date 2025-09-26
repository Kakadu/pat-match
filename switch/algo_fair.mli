module Make : functor (W : Unn_pre.WORK) (Arg : Main_inputs.ARG_FINAL) -> sig
  val work :
    n:int ->
    with_hack:bool ->
    print_examples:bool ->
    check_repeated_ifs:'a ->
    debug_filtered_by_size:bool ->
    prunes_period:int option ->
    with_default_shortcuts:bool ->
    unit

  val test :
    ?print_examples:bool ->
    ?debug_filtered_by_size:bool ->
    ?with_hack:bool ->
    ?check_repeated_ifs:bool ->
    ?prunes_period:int option ->
    ?with_default_shortcuts:bool ->
    int ->
    unit
end
