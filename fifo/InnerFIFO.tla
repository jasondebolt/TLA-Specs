----------------------------- MODULE InnerFIFO -----------------------------

EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out, q

InChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------

Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>
        
TypeInvariant == /\ InChan!TypeInvariant
                 /\ OutChan!TypeInvariant
                 /\ q \in Seq(Message)
                 
SSend(msg) == /\ InChan!Send(msg)      \* Send mes on channel 'in'.
              /\ UNCHANGED <<out, q>>
              
BufRcv == /\ InChan!Rcv                \* Receive message from channel 'in'.
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out
          
BufSend == /\ q # << >>                \* Enabled only if q is nonempty
           /\ OutChan!Send(Head(q))    \* Send Head(q) on channel 'out'
           /\ q' = Tail(q)             \*   and remove it from q.
           /\ UNCHANGED in             
     
RRcv == /\ OutChan!Rcv                  \* Receive message from channel 'out'
        /\ UNCHANGED <<in, q>>
        
Next == \/ \E msg \in Message : SSend(msg)    
        \/ BufRcv
        \/ BufSend
        \/ RRcv
        
Spec == Init /\ [][Next]_<<in, out, q>>

-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sat May 18 09:09:50 PDT 2019 by jasondebolt
\* Created Sat May 18 08:51:08 PDT 2019 by jasondebolt
