-------------------------- MODULE SingleItemTuple --------------------------
EXTENDS Sequences, Integers

VARIABLE tup

Init == /\ tup = <<1, 2, 3>>

Invariant == Len(tup) /= 1

Increase == /\ tup' = tup \o <<99>>

Decrease == /\ tup' = Tail(tup)

Next == \/ Increase
        \/ Decrease

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 14:16:57 PDT 2019 by jasondebolt
\* Created Sat Apr 20 12:15:07 PDT 2019 by jasondebolt
