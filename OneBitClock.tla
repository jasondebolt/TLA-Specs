---------------------------- MODULE OneBitClock ----------------------------
VARIABLE clock

(***************************************************************************)
(* The state predicate Init is true if the value of clock is either 0 or   *)
(* 1.                                                                      *)
(***************************************************************************)
Init == clock \in {0, 1}

(***************************************************************************)
(* The next-state relation Tick sets clock′ (the value of clock in the     *)
(* next state) to 1 if clock is 0, and 0 if clock is 1.                    *)
(***************************************************************************)
Tick == IF clock = 0 THEN clock' = 1 ELSE clock' = 0

(***************************************************************************)
(* Spec is a temporal formula asserting all behaviours of one-bit clock    *)
(* must initially satisfy Init and have all steps either match Tick or be  *)
(* stuttering steps.  Two such behaviours are: 0 -> 1 -> 0 -> 1 -> 0 ->    *)
(* ...                                                                     *)
(*                                                                         *)
(* 1 -> 0 -> 1 -> 0 -> 1 -> ...                                            *)
(***************************************************************************)
Spec == Init /\ [][Tick]_<<clock>>

=============================================================================
\* Modification History
\* Last modified Sun Apr 21 10:19:30 PDT 2019 by jasondebolt
\* Created Sun Apr 21 09:37:13 PDT 2019 by jasondebolt
