---------------------------- MODULE BoundedFIFO ----------------------------

EXTENDS Naturals, Sequences
VARIABLES in, out
CONSTANTS Message, N

ASSUME (N \in Nat) /\ (N > 0)


Inner(q) == INSTANCE InnerFIFO

BNext(q) == /\ Inner(q)!Next
            /\ Inner(q)!BufRcv => (Len(q) < N)

Spec == /\ \EE q: Inner(q)!Init /\ [][BNext(q)]_<<in, out, q>>

=============================================================================
\* Modification History
\* Last modified Sat May 18 13:44:39 PDT 2019 by jasondebolt
\* Created Sat May 18 13:08:19 PDT 2019 by jasondebolt
