------------------------------ MODULE Counter ------------------------------

EXTENDS Integers
VARIABLE N

Init == /\ N = 0
 
Count(x) == /\ x' = x + 1          
        
Next == \/ Count(N)

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 17:26:36 PDT 2019 by jasondebolt
\* Created Sat Apr 20 17:16:30 PDT 2019 by jasondebolt
