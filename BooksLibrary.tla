---------------------------- MODULE BooksLibrary ----------------------------
EXTENDS Integers, TLC, Sequences

CONSTANTS Books, People, NumCopies

(***************************************************************************)
(* Constants:                                                              *)
(*   NumCopies <- 1..1                                                     *)
(*   People <- [model value] {p1, p2}                                      *)
(*   Books <- [model value] {b1}                                           *)
(***************************************************************************)

set ++ x == set \union {x}
set -- x == set \ {x}

(*--algorithm Books

variables
  library \in [Books -> NumCopies];
  
define
  AvailableBooks == {b \in Books: library[b] > 0}
end define;
  
fair process person \in People
variables
  books = {};
begin
  Person:
    either
      \* Checkout
      with b \in AvailableBooks \ books do
        library[b] := library[b] - 1;
        books := books ++ b;
      end with;
    or
      \* Return
      with b \in books do
        library[b] := library[b] + 1;
        books := books -- b;
      end with;
    end either;
  goto Person;
end process;
  
end algorithm;
*)

\* BEGIN TRANSLATION
VARIABLES library, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}

VARIABLE books

vars == << library, pc, books >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ pc = [self \in ProcSet |-> "Person"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in AvailableBooks \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                   \/ /\ \E b \in books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

Next == (\E self \in People: person(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


TypeInvariant == 
  /\ library \in [Books -> NumCopies]
  /\ books \in [People -> SUBSET Books]


=============================================================================
\* Modification History
\* Last modified Sun May 05 15:08:30 PDT 2019 by jasondebolt
\* Created Sun May 05 14:40:09 PDT 2019 by jasondebolt
