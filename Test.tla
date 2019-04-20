-------------------------------- MODULE Test --------------------------------


EXTENDS Integers

VARIABLES a, b


TypeOK == /\ a \in 1..4
          /\ b \in 1..4

Init == /\ a = 1
        /\ b = 2


A == IF a <= 3
       THEN /\ a' = a + 1
            /\ b' = b
       ELSE /\ a' = a
            /\ b' = b

B == IF b <= 3
       THEN /\ b' = b + 1
            /\ a' = a
       ELSE /\ b' = b
            /\ a' = a
     

Next == \/ A
        \/ B


=============================================================================
\* Modification History
\* Last modified Fri Apr 19 20:44:00 PDT 2019 by jasondebolt
\* Created Fri Apr 19 13:33:34 PDT 2019 by jasondebolt
