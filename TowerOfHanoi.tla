---------------------------- MODULE TowerOfHanoi ----------------------------

EXTENDS Sequences, Integers  
VARIABLE A, B, C

CanMove(x,y) == /\ Len(x) > 0  
                /\ IF Len(y) > 0 THEN Head(y) > Head(x) ELSE TRUE

Move(x,y,z) == /\ CanMove(x,y)  
               /\ x' = Tail(x)
               /\ y' = <<Head(x)>> \o y
               /\ z' = z

Invariant == C /= <<1,2,3>>                         

Init == /\ A = <<1,2,3>>  
        /\ B = <<>>
        /\ C = <<>>

Next == \/ Move(A,B,C) \* Move A to B  
        \/ Move(A,C,B) \* Move A to C
        \/ Move(B,A,C) \* Move B to A
        \/ Move(B,C,A) \* Move B to C
        \/ Move(C,A,B) \* Move C to A
        \/ Move(C,B,A) \* Move C to B

=============================================================================
\* Modification History
\* Last modified Sun Apr 21 21:03:07 PDT 2019 by jasondebolt
\* Created Thu Apr 18 19:50:30 PDT 2019 by jasondebolt
