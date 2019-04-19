-------------------------------- MODULE Jugs --------------------------------

EXTENDS Integers
VARIABLES small, big


TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ big   = 0
        /\ small = 0


FillSmall == \/ /\ small' = 3
                /\ big' = big
        
FillBig == \/ /\ big' = 5
              /\ small' = small
              
EmptySmall == \/ /\ small' = 0
                 /\ big' = big
  
EmptyBig == \/ /\ big' = 0
               /\ small' = small              
              
SmallToBig == IF big + small =< 5
               THEN /\ big' = big + small
                    /\ small' = 0
               ELSE /\ big' = 5
                    /\ small' = small - (5 - big)
                   
BigToSmall == IF big + small =< 3
                THEN /\ small' = big + small
                     /\ big' = 0 
                ELSE /\ small' = 3
                     /\ big' = small - (3 - big)
                  
           
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

=============================================================================
\* Modification History
\* Last modified Thu Apr 18 19:25:05 PDT 2019 by jasondebolt
\* Created Thu Apr 18 16:47:35 PDT 2019 by jasondebolt
