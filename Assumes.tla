------------------------------ MODULE Assumes ------------------------------
EXTENDS Integers, Sequences, FiniteSets, Naturals

(* You can run this as a model using "No behavior spec" mode *)
\* Single line comment

ASSUME
  /\ TRUE = TRUE
  /\ ~FALSE = TRUE

Jason == "jason"
ASSUME
  Jason = "jason"

record == [name |-> "jason", age |-> 2]
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
  

(***************************************************************************)
(* Sets                                                                    *)
(***************************************************************************)

ASSUME
  {1, 2, 2, 2, 3} = {1, 2, 3}
  
ASSUME
  {1, 2, 3, 3, 4, 4} \ {4} = {1, 2, 3}
  
  
ASSUME
  {1, 2, 3} \cup {4, 5, 6} = {1, 2, 3, 4, 5, 6}
  
  
ASSUME
  \E x \in {3, 4, 5} : x = 5


ASSUME
  {1, 3} \subseteq {3, 2, 1}
  

ASSUME
  (\A i \in {2, 4, 8}: i % 2 = 0) = TRUE


ASSUME
  ({1, 2} \in SUBSET {1, 2, 3}) = TRUE


ASSUME
  ({1, 2} \in SUBSET ({1, 3} \cup {4, 2})) = TRUE
  
ASSUME
  /\ {"one", "two"} # {}
  /\ {"one", "two"} /= {}
  /\ {"one", "two"} \ {"one"} = {"two"}
  

ASSUME
  /\ IsFiniteSet({1, 2, 3})
  /\ ~IsFiniteSet(Nat)
  
  
ASSUME
  /\ Cardinality({3, 4, 1}) = 3
  /\ Cardinality({}) = 0


ASSUME
  {x \in 1..8 : x % 2 = 1} = {1, 3, 5, 7}
  
ASSUME
  {x \in 1..8 : x % 2 = 1 /\ ~(x % 5 = 0)} = {1, 3, 7}
  
  
ASSUME
  {x \in {[name |-> "jason"], [name |-> "jake"]} : x.name = "jason"} = {[name |-> "jason"]}
  
ASSUME
  {<<x, y>> \in {"a", "b"} \X {[name |-> "jason"], [name |-> "bob"]}: y.name = "jason"} = {<<"a", [name |-> "jason"]>>, <<"b", [name |-> "jason"]>>}
  
ASSUME
 {<<x, y>> \in {<<1, 2>>, <<4, 2>>} : x > y} = {<<4, 2>>}
 
 
 
(***************************************************************************)
(* IF STATEMENTS                                                           *)
(***************************************************************************)

ASSUME
  /\ (IF 1 < 3 THEN 1 ELSE 0) = 1
  /\ (IF 1 < 3 THEN IF 2 > 1 THEN 6 ELSE 4 ELSE 7) = 6
 

(***************************************************************************)
(* LET STATEMENTS                                                          *)
(***************************************************************************)


ASSUME
  /\ LET x == 6 IN x \in {6, 7}

(***************************************************************************)
(* For all y in S such that y is not prime or y is less than or equal to x *)
(***************************************************************************)

IsPrime(x) == x > 1 /\ ~\E d \in 2..(x-1) : x % d = 0


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

ASSUME
  ~\E x \in {1, 3, 5} : IsEven(x)
  
Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value)) 

Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)
          
ASSUME
  Sum({1, 2, 3}) = 6

Min(S) == CHOOSE x \in S: \A y \in S: x <= y


ASSUME
  Min({5, 3, 7, 10, 2, 9}) = 2
  
Max(S) == CHOOSE x \in S: \A y \in S: x >= y

ASSUME
  Max({4, 6, 1, 2, 9, 3, 5}) = 9
  

(***************************************************************************)
(* SEQUENCES                                                               *)
(***************************************************************************)

\* Seq(S) is the set of all finite sequences of set S.

ASSUME
  /\ <<>>     \in Seq({1, 0})  
  /\ <<1>>    \in Seq({1, 0})
  /\ <<0>>    \in Seq({1, 0})
  /\ <<0, 0>> \in Seq({1, 0})
  /\ <<0, 1>> \in Seq({1, 0})
  /\ <<1, 0>> \in Seq({1, 0})
  /\ <<1, 1>> \in Seq({1, 0})

ASSUME
  /\ {<<0>>} \subseteq Seq({0, 1})
  
ASSUME
  <<1, 2, 3>> \in Seq({1, 2, 3})
  
ASSUME
  <<4>> \notin Seq({1, 2, 3})
  
ASSUME
  <<1, 2, 3, 4>> \notin Seq({1, 2, 3})
  
 
ASSUME
  /\ <<1, 2>> \o <<3, 4>> = <<1, 2, 3, 4>>
  
 
LessThanThree(x) == x < 3
  
  
ASSUME
  /\ Head(<<2, 3, 4>>) = 2
  /\ Tail(<<2, 3, 4>>) = <<3, 4>>
  /\ Append(<<1, 2>>, 3) = <<1, 2, 3>>
  /\ Len(<<5, 2, 1>>) = 3
  /\ SubSeq(<<9, 3, 5, 6>>, 1, 3) = <<9, 3, 5>>
  /\ SelectSeq(<<5, 2, 9>>, LessThanThree) = <<2>> 

(***************************************************************************)
(* TUPLES                                                        *)
(***************************************************************************)

chessboard_squares == {"a", "b", "c", "d", "e", "f", "g", "h"} \X (1..8)

ASSUME
  /\ <<"a", 1>> \in chessboard_squares
  /\ <<"a", 2>> \in chessboard_squares
  /\ <<"a", 3>> \in chessboard_squares
  /\ <<"a", 4>> \in chessboard_squares
  
  
jason == (1..2) \X {"Jason", "DeBolt"}


ASSUME
  /\ <<1, "Jason">> \in jason
  /\ <<2, "Jason">> \in jason
  /\ <<1, "DeBolt">> \in jason
  /\ <<2, "DeBolt">> \in jason


digits == {"one", "three"} \X {"two", "four"}

ASSUME
  /\ <<"one", "two">> \in digits
  /\ <<"three", "four">> \in digits
  

ASSUME
  /\ <<"one", "two">> \o <<"three">> = <<"one", "two", "three">>
  /\ <<"one", "two">> \circ <<"three">> = <<"one", "two", "three">>
  

A == {1}
B == {2}
C == {3}

ASSUME
  /\ <<1, 2, 3>> \in A \X B \X C
  /\ <<1, <<2, 3>>>> \in A \X (B \X C)
  /\ <<<<1, 2>>, 3>> \in (A \X B) \X C
  
(***************************************************************************)
(* Structures.                                                             *)
(*                                                                         *)
(* Structures are hashes.  They have keys and values.  You specify them as *)
(* [key |-> value] and query them with either ["key"] or .key.  Both are   *)
(* legal and valid.                                                        *)
(***************************************************************************)

SomeHash == [x |-> 1, y |-> {2, 3}]

ASSUME
  /\ SomeHash.x = 1
  /\ SomeHash["x"] = 1
  /\ SomeHash.y = {2, 3}
  /\ SomeHash["y"] = {2, 3}
  /\ DOMAIN SomeHash = {"x", "y"}
  
  
SomeHash2 == [x |-> 1, y |-> {2, 3}]
SomeHash3 == [SomeHash2 EXCEPT !["x"] = 6]

ASSUME
  /\ SomeHash3.x = 6

(***************************************************************************)
(* Aside from that, there’s one extra trick structures have.  Instead of   *)
(* key |-> value, you can do key : set.  In that case, instead of a        *)
(* structure you get the set of all structures which have, for each given  *)
(* key, a value in the set.                                                *)
(***************************************************************************)

SetOfStructures == [x: {1}, y: {2, 3, 4}]

(***************************************************************************)
(* If you use : syntax and any of the values are not sets, then the entire *)
(* construct is invalid.  In other words, while [a: {1}, b: {2,3}] is the  *)
(* above set, [a: 1, b: {2, 3}] will throw an error if you try to use it.  *)
(***************************************************************************)

ASSUME
  /\ [x |-> 1, y |-> 2] \in SetOfStructures
  /\ [x |-> 1, y |-> 3] \in SetOfStructures
  /\ [x |-> 1, y |-> 4] \in SetOfStructures

  
(***************************************************************************)
(* Functions                                                               *)
(***************************************************************************)
ASSUME
  /\ [{1, 2, 3} -> {"done"}] = {<<"done", "done", "done">>}  \* Turns a function into a set of tuples
  /\ [{"a", "b"} -> {"done"}] = {[a |-> "done", b |-> "done"]}   \* Turns a function into a set of structs
  /\ [{"a", "b"} -> {"done", "pc"}] = {[a |-> "done", b |-> "done"],   \* Turns a function into a set of structs
                                       [a |-> "done", b |-> "pc"],
                                       [a |-> "pc",   b |-> "done"],
                                       [a |-> "pc",   b |-> "pc"]}
  /\ [{"p1", "p2"} -> {"a", "b", "c", "done"}] = {[p1 |-> "a",    p2 |-> "a"],
                                                  [p1 |-> "a",    p2 |-> "b"],
                                                  [p1 |-> "a",    p2 |-> "c"],
                                                  [p1 |-> "a",    p2 |-> "done"],
                                                  [p1 |-> "b",    p2 |-> "a"],
                                                  [p1 |-> "b",    p2 |-> "b"],
                                                  [p1 |-> "b",    p2 |-> "c"],
                                                  [p1 |-> "b",    p2 |-> "done"],
                                                  [p1 |-> "c",    p2 |-> "a"],
                                                  [p1 |-> "c",    p2 |-> "b"],
                                                  [p1 |-> "c",    p2 |-> "c"],
                                                  [p1 |-> "c",    p2 |-> "done"],
                                                  [p1 |-> "done", p2 |-> "a"],
                                                  [p1 |-> "done", p2 |-> "b"],
                                                  [p1 |-> "done", p2 |-> "c"],
                                                  [p1 |-> "done", p2 |-> "done"]}
  /\ [{"p1", "p2", "p3"} -> {"a", "b", "c"}] =  { [p1 |-> "a", p2 |-> "a", p3 |-> "a"],
                                                  [p1 |-> "a", p2 |-> "a", p3 |-> "b"],
                                                  [p1 |-> "a", p2 |-> "a", p3 |-> "c"],
                                                  [p1 |-> "a", p2 |-> "b", p3 |-> "a"],
                                                  [p1 |-> "a", p2 |-> "b", p3 |-> "b"],
                                                  [p1 |-> "a", p2 |-> "b", p3 |-> "c"],
                                                  [p1 |-> "a", p2 |-> "c", p3 |-> "a"],
                                                  [p1 |-> "a", p2 |-> "c", p3 |-> "b"],
                                                  [p1 |-> "a", p2 |-> "c", p3 |-> "c"],
                                                  [p1 |-> "b", p2 |-> "a", p3 |-> "a"],
                                                  [p1 |-> "b", p2 |-> "a", p3 |-> "b"],
                                                  [p1 |-> "b", p2 |-> "a", p3 |-> "c"],
                                                  [p1 |-> "b", p2 |-> "b", p3 |-> "a"],
                                                  [p1 |-> "b", p2 |-> "b", p3 |-> "b"],
                                                  [p1 |-> "b", p2 |-> "b", p3 |-> "c"],
                                                  [p1 |-> "b", p2 |-> "c", p3 |-> "a"],
                                                  [p1 |-> "b", p2 |-> "c", p3 |-> "b"],
                                                  [p1 |-> "b", p2 |-> "c", p3 |-> "c"],
                                                  [p1 |-> "c", p2 |-> "a", p3 |-> "a"],
                                                  [p1 |-> "c", p2 |-> "a", p3 |-> "b"],
                                                  [p1 |-> "c", p2 |-> "a", p3 |-> "c"],
                                                  [p1 |-> "c", p2 |-> "b", p3 |-> "a"],
                                                  [p1 |-> "c", p2 |-> "b", p3 |-> "b"],
                                                  [p1 |-> "c", p2 |-> "b", p3 |-> "c"],
                                                  [p1 |-> "c", p2 |-> "c", p3 |-> "a"],
                                                  [p1 |-> "c", p2 |-> "c", p3 |-> "b"],
                                                  [p1 |-> "c", p2 |-> "c", p3 |-> "c"] }

(***************************************************************************)
(* Type Composition                                                        *)
(*                                                                         *)
(* Any type can be squeezed inside any other type.                         *)
(***************************************************************************)

crazy == [a |-> {<<>>, <<1, 2, 3>>, <<3, 2, 1>>}, b |-> <<[a |-> 0]>>]

\* A function of keys mapping to sets of tuples or of keys mapping to tuples of functions.

ASSUME
  crazy.b[1].a = 0 \* Remember that tuples are 1 indexed.
  

blah == [name |-> "jason", hobbies |-> [outdoor |-> <<"cycling", "hiking">>, indoor |-> <<"reading", "watching tv">>]]

ASSUME
  /\ blah.name = "jason"
  /\ blah.hobbies.outdoor[1] = "cycling"
  
  
sing == <<<<4, 5, 6>>, <<>>, <<>>>>

ASSUME
  DOMAIN sing = {1, 2, 3}


=============================================================================
\* Modification History
\* Last modified Sun May 19 15:28:48 PDT 2019 by jasondebolt
\* Created Sat Apr 20 20:01:34 PDT 2019 by jasondebolt
