---------------------------- MODULE JasonLibrary ----------------------------
EXTENDS Integers

(***************************************************************************)
(* Set related                                                             *)
(***************************************************************************)

Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value))

Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)

=============================================================================
\* Modification History
\* Last modified Sun Apr 21 20:59:08 PDT 2019 by jasondebolt
\* Created Sun Apr 21 20:57:12 PDT 2019 by jasondebolt
