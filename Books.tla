
------------------------------- MODULE Books -------------------------------

EXTENDS Integers, TLC, Sequences

CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat

set ++ x == set \union {x}
set -- x == set \ {x}

(*--algorithm Books

variables
  library = \in [Books -> NumCopies];
  
define
  AvailableBooks == {b \in Books: library[b] > 0}
end define;
  
process person \in People
variables
  books = \*??
begin
  Person:
    either
      \* Checkout
      skip;
    or
      \* Return
      skip;
    end either;
  goto Person;
end process
  
end algorithm;
*)

=============================================================================
\* Modification History
\* Last modified Sun May 05 14:38:53 PDT 2019 by jasondebolt
\* Created Sun May 05 14:14:01 PDT 2019 by jasondebolt
