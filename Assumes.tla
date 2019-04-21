------------------------------ MODULE Assumes ------------------------------

(* You can run this as a model using "No behavior spec" mode *)
\* Single line comment

ASSUME
  /\ TRUE = TRUE
  /\ ~FALSE = TRUE

Jason == "jason"
ASSUME
  Jason = "jason"

record == [name |-> "jason", age |-> 37]
ASSUME
  /\ record.name = "jason"
  /\ record.name /= "foo"
  
ASSUME
  \A F \in {TRUE} : F = F
  
ASSUME
  \A F \in {FALSE} : F = F
  
ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  FALSE => TRUE = TRUE
  
ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  FALSE => FALSE = TRUE

ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  TRUE => TRUE = TRUE
  
ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  TRUE => FALSE = FALSE
  
ASSUME
  TRUE <=> TRUE
  
ASSUME
  FALSE <=> FALSE
  

ASSUME
  \A F, G \in {TRUE, FALSE} : (F => G) <=> ~F \/ G
  

ASSUME
  {1, 2, 2, 2, 3} = {1, 2, 3}
  
  
ASSUME
  {1, 2, 3, 3, 4, 4} \ {4} = {1, 2, 3}
  
  
ASSUME
  \E x \in {3, 4, 5} : x = 5


ASSUME 
  {1, 3} \subseteq {3, 2, 1}

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 21:11:19 PDT 2019 by jasondebolt
\* Created Sat Apr 20 20:01:34 PDT 2019 by jasondebolt
