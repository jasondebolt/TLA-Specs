-------------------------------- MODULE Door --------------------------------

(*--algorithm door
variables
  opened = FALSE,
  locked = FALSE,
  key \in BOOLEAN;
  
process open_door = "Opened Door"
begin
  OpenedDoor: \* Things you can do when the door is already opened.
    await opened;
    either \* lock/unlock
      locked := ~locked
    or \* close the door
      await ~locked;
      opened := FALSE;
    end either;
    goto OpenedDoor;
end process;

process closed_door = "Closed Door"
begin
  ClosedDoor: \* Things you can do when the door is already closed.
    await ~opened;
    either \* lock/unlock
      await key;
      locked := ~locked;
    or \* open the door
      await ~locked;
      opened := TRUE;
    end either;
    goto ClosedDoor;
end process;

end algorithm;
*)      
           
        
      
\* BEGIN TRANSLATION
VARIABLES opened, locked, key, pc

vars == << opened, locked, key, pc >>

ProcSet == {"Opened Door"} \cup {"Closed Door"}

Init == (* Global variables *)
        /\ opened = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = [self \in ProcSet |-> CASE self = "Opened Door" -> "OpenedDoor"
                                        [] self = "Closed Door" -> "ClosedDoor"]

OpenedDoor == /\ pc["Opened Door"] = "OpenedDoor"
              /\ opened
              /\ \/ /\ locked' = ~locked
                    /\ UNCHANGED opened
                 \/ /\ ~locked
                    /\ opened' = FALSE
                    /\ UNCHANGED locked
              /\ pc' = [pc EXCEPT !["Opened Door"] = "OpenedDoor"]
              /\ key' = key

open_door == OpenedDoor

ClosedDoor == /\ pc["Closed Door"] = "ClosedDoor"
              /\ ~opened
              /\ \/ /\ key
                    /\ locked' = ~locked
                    /\ UNCHANGED opened
                 \/ /\ ~locked
                    /\ opened' = TRUE
                    /\ UNCHANGED locked
              /\ pc' = [pc EXCEPT !["Closed Door"] = "ClosedDoor"]
              /\ key' = key

closed_door == ClosedDoor

Next == open_door \/ closed_door
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sun May 05 11:27:05 PDT 2019 by jasondebolt
\* Created Sun May 05 10:55:20 PDT 2019 by jasondebolt
