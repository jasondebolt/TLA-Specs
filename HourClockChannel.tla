-------------------------- MODULE HourClockChannel --------------------------

(***************************************************************************)
(* 1.  (a) Write a specification of an hour-clock that sends the time to   *)
(*    the environment over a channel chan.  The specification should make  *)
(*    use of the definitions from the Channel and HourClock modules by     *)
(*    incorporating them with an EXTENDS statement.  Write two versions    *)
(*    of the specification.                                                *)
(*                                                                         *)
(*       Version 1: The clock can tick at any time.                        *)
(*                                                                         *)
(*       Version 2: The clock cannot tick between sending a value on chan  *)
(*                  and the receipt of that value by the environment.      *)
(*                                                                         *)
(*    Include type invariants and use TLC to check them.                   *)
(*                                                                         *)
(*    (b) Use TLC to check that the Version 1 specification implements     *)
(*    the Channel specification with Data replaced by 1..12.  That is,     *)
(*    every behavior allowed by your specification satisfies the specification *)
(*    Spec of module Channel, with Data replaced by the set 1..12.         *)
(*    Use TLC to check that Version 2 implements the specification         *)
(*    HourClockChannel that you wrote in Exercise 1 of folder              *)
(*    AsynchronousInterface.                                               *)
(*                                                                         *)
(*    (c) Write specifications that hides the clock in the specifications  *)
(*    of part (a).  Explain informally why the resulting specification     *)
(*    is equivalent to:                                                    *)
(*                                                                         *)
(*       - The Channel specification with Data replaced by 1..12, for      *)
(*         Version 1.                                                      *)
(*                                                                         *)
(*       - The HourClockChannel specification, for Version 2.              *)
(***************************************************************************)

EXTENDS Naturals, HourClock, Channel, TLC

-----------------------------------------------------------------------------

PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)

IsSending == chan.rdy # chan.ack

HCChannelInit == /\ Init         \* Initialize Channel
                 /\ HCini        \* Initilized HourClock   
        
HCChannelSend(d) == /\ Send(d)   \* Channel's Send(d)
                    /\ UNCHANGED <<hr>>

HCChannelRcv     == /\ Rcv       \* Channel's Rcv
                    /\ UNCHANGED <<hr>>
           
HCnxtChannel  == /\ HCnxt        \* HourClock's NCnxt
                 /\ ~IsSending
                 /\ UNCHANGED <<chan>>
                 /\ PrintVal("HCnxtChannel", <<hr, chan>>)
           
HCChannelNext    == (\E d \in Data : HCChannelSend(d)) \/ HCChannelRcv \/ HCnxtChannel

HCChannelSpec    == HCChannelInit /\ [][HCChannelNext]_<<chan, hr>>

-----------------------------------------------------------------------------
THEOREM HCChannelSpec => []TypeInvariant



=============================================================================
\* Modification History
\* Last modified Sat May 18 12:16:33 PDT 2019 by jasondebolt
\* Created Sat May 18 09:31:23 PDT 2019 by jasondebolt
