------------------------------ MODULE Assumes ------------------------------
EXTENDS Integers, Sequences

(* You can run this as a model using "No behavior spec" mode *)
\* Single line comment

ASSUME
  /\ TRUE = TRUE
  /\ ~FALSE = TRUE

Jason == "jason"
ASSUME
  Jason = "jason"

record == [name |-> "jason", age |-> 37]
ASSUME
  /\ record.name = "jason"
  /\ record.name /= "foo"
  
ASSUME
  \A F \in {TRUE} : F = F
  
ASSUME
  \A F \in {FALSE} : F = F
  
ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  FALSE => TRUE = TRUE
  
ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  FALSE => FALSE = TRUE

ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  TRUE => TRUE = TRUE
  
ASSUME \* => means "implies", as in A => B is "(not A) OR B"
  TRUE => FALSE = FALSE
  
ASSUME
  TRUE <=> TRUE
  
ASSUME
  FALSE <=> FALSE
  

ASSUME
  \A F, G \in {TRUE, FALSE} : (F => G) <=> ~F \/ G
  

ASSUME
  {1, 2, 2, 2, 3} = {1, 2, 3}
  
  
ASSUME
  {1, 2, 3, 3, 4, 4} \ {4} = {1, 2, 3}
  
  
ASSUME
  \E x \in {3, 4, 5} : x = 5


ASSUME 
  {1, 3} \subseteq {3, 2, 1}
  

IsPrime(x) == x > 1 /\ ~\E d \in 2..(x-1) : x % d = 0

(***************************************************************************)
(* For all y in S such that y is not prime or y is less than or equal to x *)
(***************************************************************************)
LargestPrime(S) == CHOOSE x \in S:
                    /\ IsPrime(x)
                    /\ \A y \in S:
                        IsPrime(y) => y <= x
                    \* or y > x => ~IsPrime(y)

ASSUME
  LargestPrime({1, 2, 3, 4, 5, 6, 7, 8, 9, 10}) = 7
  

IsEven(x) == x % 2 = 0

LargetEven(S) == CHOOSE x \in S:
                  /\ IsEven(x)
                  /\ \A y \in S:
                     IsEven(y) => y <= x

ASSUME
  LargetEven({1, 2, 3, 4, 5, 5, 5}) = 4
  

ASSUME
  \A x \in {}: FALSE

ASSUME
  \A x \in {}: TRUE
  
ASSUME
  \A x \in {}: 7
  
ASSUME
  \A x \in {FALSE}: TRUE

ASSUME
  \A x \in {TRUE}: TRUE
  
ASSUME
  (\A x \in {FALSE}: FALSE) = FALSE
  

IsCommutative(Op(_,_), S) == \A x \in S :
                           \A y \in S : Op(x,y) = Op(y,x)
  
Add(x, y) == x + y
Divide(x, y) == x \div y

ASSUME
  IsCommutative(Add, {1, 2, 3})
  
ASSUME
  IsCommutative(Divide, {1, 2, 3}) = FALSE
    
ASSUME
  IsCommutative(Divide, {1, 2, 3}) => FALSE
  
ASSUME
  IsCommutative(Divide, {1, 2, 3}) => TRUE
  
ASSUME
  ~IsCommutative(Divide, {1, 2, 3})
  

  

=============================================================================
\* Modification History
\* Last modified Sun Apr 21 11:41:10 PDT 2019 by jasondebolt
\* Created Sat Apr 20 20:01:34 PDT 2019 by jasondebolt
