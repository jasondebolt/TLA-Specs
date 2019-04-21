-------------------------------- MODULE Orders --------------------------------

EXTENDS Integers
VARIABLE orderState, Id

Init == /\ orderState = "none" /\ Id \in 1..100


Order(x) == /\ orderState = "none" /\ orderState' = "ordered" /\ Id' = x
Ship(x) == /\ orderState = "ordered" /\ orderState' = "shipped" /\ Id' = x
Cancel(x) == /\ orderState = "shipped" /\ orderState' = "cancelled" /\ Id' = x
 
Invariant == /\ Id /= 45
   
Next == \/ Order(Id) \/ Ship(Id) \/ Cancel(Id)


=============================================================================
\* Modification History
\* Last modified Sat Apr 20 17:50:16 PDT 2019 by jasondebolt
\* Created Sat Apr 20 17:30:10 PDT 2019 by jasondebolt
