-------------------------- MODULE OperationsTo311 --------------------------

EXTENDS Integers
VARIABLES num


Init == /\ num = 0


AddTwo == IF num =< 400
            THEN /\ num' = num + 2
          ELSE /\ num' = num
          

MultByThree == IF num <= 400
                THEN /\ num' = num * 3
               ELSE /\ num' = num

Next == \/ AddTwo
        \/ MultByThree

=============================================================================
\* Modification History
\* Last modified Thu Apr 18 19:52:16 PDT 2019 by jasondebolt
\* Created Thu Apr 18 19:37:41 PDT 2019 by jasondebolt
