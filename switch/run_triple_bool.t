  $ export NOBENCH=1
  $ ./main_switch.exe -triple_bool
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | triple (_, false, true) -> 1 
  | triple (false, true, _) -> 2 
  | triple (_, _, false) -> 3 
  | triple (_, _, true) -> 4 
  A priori answer:
  
  (match S[2] with
   | true -> (match S[1] with
              | false -> 1 
              | _ -> (match S[1] with
                      | true -> (match S[0] with
                                 | false -> 2 
                                 | _ -> (match S[2] with
                                         | false -> 3 
                                         | _ -> (match S[2] with
                                                 | true -> 4 
                                                 | _ -> fail)))
                      | _ -> (match S[2] with
                              | false -> 3 
                              | _ -> (match S[2] with
                                      | true -> 4 
                                      | _ -> fail))))
   | _ -> (match S[1] with
           | true -> (match S[0] with
                      | false -> 2 
                      | _ -> (match S[2] with
                              | false -> 3 
                              | _ -> (match S[2] with
                                      | true -> 4 
                                      | _ -> fail)))
           | _ -> (match S[2] with
                   | false -> 3 
                   | _ -> (match S[2] with
                           | true -> 4 
                           | _ -> fail))))
  Initial upper bound of IF-ish constructions = 14
  		max_matchable_height = 2
  		max_nested_switches = 4
  		prunes_period = 100
  	S[1] -> [ 2=true; 3=false]
  	S[2] -> [ 2=true; 3=false]
  	S[0] -> [ 2=true; 3=false]
  Testing 8 examples:
    triple [true; true; true] ~~> Some (4)
    triple [false; true; true] ~~> Some (2)
    triple [true; false; true] ~~> Some (1)
    triple [true; true; false] ~~> Some (3)
    triple [false; false; true] ~~> Some (1)
    triple [false; true; false] ~~> Some (2)
    triple [true; false; false] ~~> Some (3)
    triple [false; false; false] ~~> Some (3)
  fair lozovML (bool*bool*bool (Maranget;page1)), all answers {
  Set upper bound of IF-ish constructions to 6
  q=(switch S with
   | _ -> (switch S with
           | _ -> (switch S with
                   | _ -> 3))) with ifs_low='6'
  ;
  Set upper bound of IF-ish constructions to 5
  q=(switch S with
   | _ -> (switch S with
           | _ -> (switch S with
                   | _ -> 3))) with ifs_low='5'
  ;
  Set upper bound of IF-ish constructions to 4
  q=(switch S with
   | _ -> (switch S with
           | _ -> 3)) with ifs_low='4'
  ;
  }
  
  with fresh = 1819
  	S[0] -> 1077
  	S[1] -> 902
  	S[2] -> 452
