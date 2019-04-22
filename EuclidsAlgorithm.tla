-------------------------- MODULE EuclidsAlgorithm --------------------------
EXTENDS Integers

VARIABLE x, y

Init == /\ x = 1024
        /\ y = 400
        
(***************************************************************************)
(* Euclid's Algorithm for finding the greatest common divisor of two       *)
(* numbers.                                                                *)
(***************************************************************************)
      
Next == \/ /\ x > y
           /\ x' = x - y
           /\ y' = y
        \/ /\ y > x
           /\ y' = y - x
           /\ x' = x

Invariant == x /= y

=============================================================================
\* Modification History
\* Last modified Sun Apr 21 20:37:03 PDT 2019 by jasondebolt
\* Created Sun Apr 21 20:36:34 PDT 2019 by jasondebolt
