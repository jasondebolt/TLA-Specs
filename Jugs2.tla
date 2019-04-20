------------------------------- MODULE Jugs2 -------------------------------

EXTENDS Integers
VARIABLES small, big


TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ big   = 0
        /\ small = 0

FillSmall == /\ small' = 3
             /\ big' = big
        
FillBig == /\ big' = 5
           /\ small' = small
              
EmptySmall == /\ small' = 0
              /\ big' = big
  
EmptyBig == /\ big' = 0
            /\ small' = small              
              
SmallToBig == \/ /\ big + small =< 5
                 /\ big' = big + small
                 /\ small' = 0
              \/ /\ big' = 5
                 /\ small' = small - (5 - big)
                   
BigToSmall == \/ /\ big + small =< 3
                 /\ small' = big + small
                 /\ big' = 0 
              \/ /\ small' = 3
                 /\ big' = small - (3 - big)
                  
           
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 10:25:14 PDT 2019 by jasondebolt
\* Created Sat Apr 20 10:18:35 PDT 2019 by jasondebolt
