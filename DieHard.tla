------------------------------ MODULE DieHard ------------------------------

EXTENDS Integers
VARIABLES small, big

(***************************************************************************)
(* In the movie Die Hard 3, our heros, John McClain (Bruce Willis) and     *)
(* Zeus (Samuel L.  Jackson), are at the bidding of the evil Peter Krieg   *)
(* (Jeremy Irons).  First they are sent to the pay phone, then to the      *)
(* subway, and finally to the park.  It is here that they must make        *)
(* exactly four gallons from five and three gallon jugs.  They did it just *)
(* in time.                                                                *)
(***************************************************************************)

TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ big   = 0
        /\ small = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small

SmallToBig == \/ /\ big + small =< 5
                 /\ big' = big + small
                 /\ small' = 0
              \/ /\ big' = 5
                 /\ small' = small - (5 - big)

BigToSmall == \/ /\ big + small =< 3
                 /\ small' = big + small
                 /\ big' = 0
              \/ /\ small' = 3
                 /\ big' = small - (3 - big)

Invariant == big /= 4

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall


=============================================================================
\* Modification History
\* Last modified Sun Apr 21 21:08:41 PDT 2019 by jasondebolt
\* Created Sun Apr 21 21:07:02 PDT 2019 by jasondebolt
