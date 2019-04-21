--------------------------- MODULE ListExtension ---------------------------

EXTENDS Integers, Sequences

VARIABLE List, Map, State

Init == /\ List = <<>>
        /\ Map = [ a |-> 4, b |-> 5, c |-> 6 ]
        /\ State = "A"
 
ExtendListA == /\ State = "A"
               /\ List' = Append(List, Map["a"])
               /\ UNCHANGED <<Map>>
               /\ State' = "B"

ExtendListB == /\ State = "B"
               /\ List' = Append(List, Map["b"])
               /\ UNCHANGED <<Map>>
               /\ State' = "C"
               
ExtendListC == /\ State = "C"
               /\ List' = Append(List, Map["c"])
               /\ UNCHANGED <<Map>>     
               /\ State' = "A"          

Invariant == /\ Len(List) /= 20     
        
Next == \/ ExtendListA \/ ExtendListB \/ ExtendListC


=============================================================================
\* Modification History
\* Last modified Sat Apr 20 19:14:07 PDT 2019 by jasondebolt
\* Created Sat Apr 20 17:51:14 PDT 2019 by jasondebolt
