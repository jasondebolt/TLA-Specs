--------------------------- MODULE AsyncInterface ---------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE val, rdy, ack

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

-----------------------------------------------------------------------------
Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy
        
Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED <<val, rdy>>
       
Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Thu May 16 13:28:08 PDT 2019 by jasondebolt
\* Created Thu May 16 13:24:20 PDT 2019 by jasondebolt
