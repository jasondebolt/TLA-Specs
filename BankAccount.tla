---------------------------- MODULE BankAccount ----------------------------

EXTENDS Naturals, TLC

VARIABLES alice_account, bob_account, money, pc

vars == << alice_account, bob_account, money, pc >>

Init == (* globals *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money = 5
        /\ pc = "A"
        
A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>
     
B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, money >>
     
Next == A \/ B 
          \/ (* Disjunct to prevent deadlock on termination *)
             (pc = "Done" /\ UNCHANGED vars)
          
Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")         
     


=============================================================================
\* Modification History
\* Last modified Fri Apr 19 14:03:55 PDT 2019 by jasondebolt
\* Created Fri Apr 19 13:56:04 PDT 2019 by jasondebolt
