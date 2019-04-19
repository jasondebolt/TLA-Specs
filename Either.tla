------------------------------- MODULE Either -------------------------------
EXTENDS Integers

(* --algorithm either_example
variables x = 3, i = 2;
begin
while i > 0 do
  either 
    x := x + 2;
  or 
    x := x * 2;
  end either;
  i := i - 1;
end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, i, pc

vars == << x, i, pc >>

Init == (* Global variables *)
        /\ x = 3
        /\ i = 2
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i > 0
               THEN /\ \/ /\ x' = x + 2
                       \/ /\ x' = x * 2
                    /\ i' = i - 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, i >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Apr 19 11:39:42 PDT 2019 by jasondebolt
\* Created Fri Apr 19 11:35:18 PDT 2019 by jasondebolt
