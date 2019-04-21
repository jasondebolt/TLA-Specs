-------------------------------- MODULE ABC --------------------------------

EXTENDS Integers
VARIABLE pc, counter

Init == /\ pc = "A" /\ counter = 0
 
A == /\ pc = "A" /\ pc' = "B" /\ counter' = counter + 1
B == /\ pc = "B" /\ pc' = "C" /\ UNCHANGED <<counter>>
C == /\ pc = "C" /\ pc' = "A" /\ UNCHANGED <<counter>>
         
Invariant == /\ counter /= 10        
   
Next == \/ A \/ B \/ C


=============================================================================
\* Modification History
\* Last modified Sat Apr 20 17:35:05 PDT 2019 by jasondebolt
\* Created Sat Apr 20 17:30:10 PDT 2019 by jasondebolt
