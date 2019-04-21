----------------------------- MODULE Turnstile -----------------------------

EXTENDS Sequences, Integers  
VARIABLE state
      
(**************************************************************************)
(* Example of a very simple 'Turnstile' finite state machine.             *)
(**************************************************************************)                      

TypeOK == state \in {"locked", "unlocked"}

Init == state = "locked"

(***************************************************************************)
(* We now define the actions that may be performed by turnstile users.     *)
(***************************************************************************)
CoinFromLocked == /\ state = "locked"
                  /\ state' = "unlocked"

CoinFromUnlocked == /\ state = "unlocked"
                    /\ state' = "unlocked"

PushFromLocked == /\ state = "locked"
                  /\ state' = "locked"

PushFromUnlocked == /\ state = "unlocked"
                    /\ state' = "locked"

(***************************************************************************)
(* The next-state action.                                                  *)
(***************************************************************************)
Next == \/ CoinFromLocked
        \/ CoinFromUnlocked
        \/ PushFromLocked
        \/ PushFromUnlocked
 
(***************************************************************************)
(* The complete specification of the system.                               *)
(***************************************************************************)       
Spec == Init /\ [][Next]_state

(***************************************************************************)
(*  Asserts that TypeOK is an invariant of the system.                     *)
(***************************************************************************)
THEOREM Spec => [](TypeOK)
=============================================================================
\* Modification History
\* Last modified Sun Apr 21 12:00:41 PDT 2019 by jasondebolt
\* Created Sat Apr 20 21:23:15 PDT 2019 by jasondebolt
