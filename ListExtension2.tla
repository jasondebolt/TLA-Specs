--------------------------- MODULE ListExtension2 ---------------------------
EXTENDS Integers, Sequences

VARIABLE List, Map, State

Init == /\ List = <<>>
        /\ Map = [ name |-> "Jason", age |-> 37 ]
        /\ State = "A"
 
ExtendListName == /\ State = "A"
                  /\ List' = Append(List, Map.name)            
                  /\ UNCHANGED <<Map>>
                  /\ State' = "B"

ExtendListAge == /\ State = "B"
                 /\ List' = Append(List, Map.age)
                 /\ UNCHANGED <<Map>>
                 /\ State' = "A"
                      
ExtendListDoubleAge == /\ State = "B"
                       /\ List' = Append(List, Map.age * 2)
                       /\ UNCHANGED <<Map>>
                       /\ State' = "A"


Invariant == /\ Len(List) /= 20     
        
Next == \/ ExtendListName \/ ExtendListAge \/ ExtendListDoubleAge



=============================================================================
\* Modification History
\* Last modified Sat Apr 20 19:31:11 PDT 2019 by jasondebolt
\* Created Sat Apr 20 19:18:37 PDT 2019 by jasondebolt
