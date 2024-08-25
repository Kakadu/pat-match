  $ export NOBENCH=1
  $ ./main_switch.exe -abc
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | A -> 1 
  | B -> 1 
  | C -> 0 
  A priori answer:
  (match S with
                                                                 | A -> 1 
                                                                 | _ -> 
                                                                 (match S with
                                                                  | B -> 1 
                                                                  | _ -> 
                                                                  (match S with
                                                                   | C -> 0 
                                                                   | _ -> fail)))
  Initial upper bound of IF-ish constructions = 3
  		max_matchable_height = 1
  		max_nested_switches = 1
  		prunes_period = 100
  	S -> [ 8=A; 9=B; 10=C]
  Testing 3 examples:
    A ~~> Some (1)
    B ~~> Some (1)
    C ~~> Some (0)
  fair lozovML (A|B|C), all answers {
  Set upper bound of IF-ish constructions to 2
  q=(switch S with
   | _ -> 0) with ifs_low='2'
  ;
  Set upper bound of IF-ish constructions to 1
  q=(switch S with
   | _ -> 1) with ifs_low='1'
  ;
  }
  
  with fresh = 12
  	S -> 7
  $ ./main_switch.exe -pair_true_false
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | pair (true, _) -> 1 
  | pair (_, true) -> 1 
  | pair (false, false) -> 0 
  A priori answer:
  
  (match S[0] with
   | true -> 1 
   | _ -> (match S[1] with
           | true -> 1 
           | _ -> (match S[1] with
                   | false -> (match S[0] with
                               | false -> 0 
                               | _ -> fail)
                   | _ -> fail)))
  Initial upper bound of IF-ish constructions = 4
  		max_matchable_height = 2
  		max_nested_switches = 3
  		prunes_period = 100
  	S[0] -> [ 2=true; 3=false]
  	S[1] -> [ 2=true; 3=false]
  Testing 4 examples:
    pair [true; true] ~~> Some (1)
    pair [false; true] ~~> Some (1)
    pair [true; false] ~~> Some (1)
    pair [false; false] ~~> Some (0)
  fair lozovML (bool*bool), all answers {
  Set upper bound of IF-ish constructions to 2
  q=(switch S with
   | _ -> (switch S with
           | _ -> 0)) with ifs_low='2'
  ;
  }
  
  with fresh = 25
  	S[0] -> 8
  	S[1] -> 7
  $ ./main_switch.exe -true_alse
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | true -> 1 
  | false -> 0 
  A priori answer:
  (match S with
                                                              | true -> 1 
                                                              | _ -> (match 
                                                                      S with
                                                                      | 
                                                                      false -> 0 
                                                                      | _ -> fail))
  Initial upper bound of IF-ish constructions = 2
  		max_matchable_height = 1
  		max_nested_switches = 1
  		prunes_period = 100
  	S -> [ 2=true; 3=false]
  Testing 2 examples:
    true ~~> Some (1)
    false ~~> Some (0)
  fair lozovML (bool), all answers {
  Set upper bound of IF-ish constructions to 1
  q=(switch S with
   | _ -> 0) with ifs_low='1'
  ;
  }
  
  with fresh = 5
  	S -> 1
  $ ./main_switch.exe -peano
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | pair (succ (_), succ (_)) -> 30 
  | pair (zero, _) -> 10 
  | pair (_, zero) -> 10 
  A priori answer:
  
  (match S[1] with
   | succ -> (match S[0] with
              | succ -> 30 
              | _ -> (match S[0] with
                      | zero -> 10 
                      | _ -> (match S[1] with
                              | zero -> 10 
                              | _ -> fail)))
   | _ -> (match S[0] with
           | zero -> 10 
           | _ -> (match S[1] with
                   | zero -> 10 
                   | _ -> fail)))
  Initial upper bound of IF-ish constructions = 6
  		max_matchable_height = 2
  		max_nested_switches = 5
  		prunes_period = always
  	S[0] -> [ 0=zero; 1=succ]
  	S[1] -> [ 0=zero; 1=succ]
  Testing 4 examples:
    pair [zero; zero] ~~> Some (10)
    pair [succ [zero]; zero] ~~> Some (10)
    pair [zero; succ [zero]] ~~> Some (10)
    pair [succ [zero]; succ [zero]] ~~> Some (30)
  fair lozovML (simple nats (a la Maranget2008)), all answers {
  Set upper bound of IF-ish constructions to 2
  q=(switch S with
   | _ -> (switch S with
           | _ -> 30)) with ifs_low='2'
  ;
  }
  
  with fresh = 14
  	S[0] -> 8
  	S[1] -> 7
  $ ./main_switch.exe -simple_list
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | pair (nil, _) -> 10 
  | pair (_, nil) -> 20 
  | pair (cons (_, _), cons (_, _)) -> 30 
  A priori answer:
  
  (match S[0] with
   | nil -> 10 
   | _ -> (match S[1] with
           | nil -> 20 
           | _ -> (match S[1] with
                   | cons -> (match S[0] with
                              | cons -> 30 
                              | _ -> fail)
                   | _ -> fail)))
  Initial upper bound of IF-ish constructions = 4
  		max_matchable_height = 2
  		max_nested_switches = 7
  		prunes_period = 100
  	S[0] -> [ 4=nil; 5=cons]
  	S[1] -> [ 4=nil; 5=cons]
  Testing 4 examples:
    pair [nil; nil] ~~> Some (10)
    pair [cons [int; nil]; nil] ~~> Some (20)
    pair [nil; cons [int; nil]] ~~> Some (10)
    pair [cons [int; nil]; cons [int; nil]] ~~> Some (30)
  fair lozovML (simple lists (from Maranget2008)), 10 answers {
  Set upper bound of IF-ish constructions to 2
  q=(switch S with
   | _ -> (switch S with
           | _ -> 30)) with ifs_low='2'
  ;
  }
  
  with fresh = 18
  	S[0] -> 9
  	S[1] -> 3
  $ ./main_switch.exe -pcf
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | triple (_, _, cons (Ldi (_), _)) -> 1 
  | triple (_, _, cons (Push, _)) -> 2 
  Initial upper bound of IF-ish constructions = 6
  		max_matchable_height = 3
  		max_nested_switches = 7
  		prunes_period = 777
  	S[2] -> [ 4=nil; 5=cons]
  	S[2][0] -> [ 14=Push; 16=Ldi; 23=IOp; 26=Int]
  Testing 5 examples:
    triple [Push; nil; nil] ~~> None
    triple [Push; nil; cons [Push; nil]] ~~> Some (2)
    triple [Push; nil; cons [Ldi [42]; nil]] ~~> Some (1)
    triple [Push; nil; cons [IOp [42]; nil]] ~~> None
    triple [Push; nil; cons [Int [42]; nil]] ~~> None
  fair lozovML (BIG (no cons -- use WCs)), all answers {
  Set upper bound of IF-ish constructions to 3
  q=(switch S with
   | _ -> (switch S with
           | _ -> fail)) with ifs_low='3'
  ;
  }
  
  with fresh = 29
  	S[2][0] -> 14
  	S[2] -> 18
