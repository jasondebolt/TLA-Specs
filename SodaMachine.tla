---------------------------- MODULE SodaMachine ----------------------------
EXTENDS Integers, Sequences

CONSTANT SODA_COST, ACCEPTED_CHANGE

VARIABLE change

TypeOK == change >= 0

Init == change = 0

AddMoney(m) == /\ change' = change + m

DispenseAndReturnChange == /\ change >= SODA_COST
                           /\ change' = change - SODA_COST

Next ==
    \/ \E m \in ACCEPTED_CHANGE: AddMoney(m)
    \/ DispenseAndReturnChange

Invariant == change /= 97


Spec == Init /\ [][Next]_<<change>>

THEOREM Spec => [](TypeOK)

=============================================================================
\* Modification History
\* Last modified Fri Sep 27 22:50:46 PDT 2019 by jasondebolt
\* Created Fri Sep 27 20:22:09 PDT 2019 by jasondebolt
