  $ export NOBENCH=1
  $ ./main_switch.exe -two_nil_lists
  Benchmarking is on=false
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  match ... with
  | pair (nil, _) -> 10 
  | pair (_, nil) -> 20 
  | pair (nil2, _) -> 30 
  | pair (_, nil2) -> 40 
  | pair (cons (_, _), cons (_, _)) -> 60 
  A priori answer:
  
  (match S[0] with
   | nil -> 10 
   | _ -> (match S[1] with
           | nil -> 20 
           | _ -> (match S[0] with
                   | nil2 -> 30 
                   | _ -> (match S[1] with
                           | nil2 -> 40 
                           | _ -> (match S[1] with
                                   | cons -> (match S[0] with
                                              | cons -> 60 
                                              | _ -> fail)
                                   | _ -> fail)))))
  Initial upper bound of IF-ish constructions = 6
  		max_matchable_height = 2
  		max_nested_switches = 7
  		prunes_period = 100
  	S[0] -> [ 4=nil; 5=cons; 6=nil2]
  	S[1] -> [ 4=nil; 5=cons; 6=nil2]
  Testing 9 examples:
    pair [nil; nil] ~~> Some (10)
    pair [nil; nil2] ~~> Some (10)
    pair [nil2; nil] ~~> Some (20)
    pair [nil; cons [int; nil]] ~~> Some (10)
    pair [nil2; nil2] ~~> Some (30)
    pair [cons [int; nil]; nil] ~~> Some (20)
    pair [cons [int; nil]; nil2] ~~> Some (40)
    pair [nil2; cons [int; nil]] ~~> Some (30)
    pair [cons [int; nil]; cons [int; nil]] ~~> Some (60)
  fair lozovML (two-nil lists (with cons)), 10 answers {
  Set upper bound of IF-ish constructions to 5
  q=(switch S with
   | _ -> (switch S with
           | _ -> 60)) with ifs_low='5'
  ;
  }
  
  with fresh = 595
  	S[0] -> 517
  	S[1] -> 499
