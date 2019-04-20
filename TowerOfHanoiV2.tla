--------------------------- MODULE TowerOfHanoiV2 ---------------------------

EXTENDS Integers, Sequences
VARIABLE A, B, C

Init == /\ A = <<1, 2, 3>>
        /\ B = <<>>
        /\ C = <<>>
  
CanMove(x, y, z) == \/ /\ Len(x) > 0
                       /\ Len(y) > 0
                       /\ Head(x) < Head(y)
                    \/ /\ Len(x) > 0
                       /\ Len(y) = 0
                    \/ FALSE
                    
 
Move(x, y, z) == \/ /\ CanMove(x, y, z)
                    /\ x' = Tail(x)
                    /\ y' = <<Head(x)>> \o y  
                    /\ z' = z
            
        
Invariant == /\ Len(C) /= 3        
        
Next == \/ Move(A, B, C)
        \/ Move(A, C, B)
        \/ Move(C, B, A)
        \/ Move(C, A, B)
        \/ Move(B, A, C)
        \/ Move(B, C, A)

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 15:27:30 PDT 2019 by jasondebolt
\* Created Sat Apr 20 15:21:53 PDT 2019 by jasondebolt
