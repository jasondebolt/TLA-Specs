----------------------------- MODULE Turnstile -----------------------------

EXTENDS Sequences, Integers  
VARIABLE state
                       
(* Example of a very simple 'Turnstile' finite state machine *)

Init == /\ state = "locked"


CoinFromLocked == /\ state = "locked"
                  /\ state' = "unlocked"

CoinFromUnlocked == /\ state = "unlocked"
                    /\ state' = "unlocked"

PushFromLocked == /\ state = "locked"
                  /\ state' = "locked"

PushFromUnlocked == /\ state = "unlocked"
                    /\ state' = "locked"

Next == \/ CoinFromLocked
        \/ CoinFromUnlocked
        \/ PushFromLocked
        \/ PushFromUnlocked

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 21:40:06 PDT 2019 by jasondebolt
\* Created Sat Apr 20 21:23:15 PDT 2019 by jasondebolt
