----------------------------- MODULE HelloWorld -----------------------------

EXTENDS Integers

(* --algorithm example
variables x \in 1..5
begin
 Add:
  x := x + 1;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..5
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ x' = x + 1
       /\ pc' = "Done"

Next == Add
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Apr 18 22:29:26 PDT 2019 by jasondebolt
\* Created Thu Apr 18 22:12:44 PDT 2019 by jasondebolt
