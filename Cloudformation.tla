--------------------------- MODULE Cloudformation ---------------------------

(***************************************************************************)
(* CloudFormation an AWS service that provisions AWS cloud infrastructure. *)
(* Infrastructure is provisioned in related groupings called "stacks."     *)
(* These stacks can be in one of several states.  This spec verifies that  *)
(* all state transitions are accounted for and that no deadlock (a state   *)
(* that has no further possible action) can occur.                         *)
(***************************************************************************)

CONSTANTS CREATE_COMPLETE,
          CREATE_IN_PROGRESS,
          CREATE_FAILED,
          DELETE_COMPLETE,
          DELETE_FAILED,
          DELETE_IN_PROGRESS,
          REVIEW_IN_PROGRESS,
          ROLLBACK_COMPLETE,
          ROLLBACK_FAILED,
          ROLLBACK_IN_PROGRESS,
          UPDATE_COMPLETE,
          UPDATE_COMPLETE_CLEANUP_IN_PROGRESS,
          UPDATE_IN_PROGRESS,
          UPDATE_ROLLBACK_COMPLETE,
          UPDATE_ROLLBACK_COMPLETE_CLEANUP_IN_PROGRESS,
          UPDATE_ROLLBACK_FAILED,
          UPDATE_ROLLBACK_IN_PROGRESS

VARIABLES status

vars == <<status>>

TypeInvariant == status \in {
    CREATE_COMPLETE,
    CREATE_IN_PROGRESS,
    CREATE_FAILED,
    DELETE_COMPLETE,
    DELETE_FAILED,
    DELETE_IN_PROGRESS,
    REVIEW_IN_PROGRESS,
    ROLLBACK_COMPLETE,
    ROLLBACK_FAILED,
    ROLLBACK_IN_PROGRESS,
    UPDATE_COMPLETE,
    UPDATE_COMPLETE_CLEANUP_IN_PROGRESS,
    UPDATE_IN_PROGRESS,
    UPDATE_ROLLBACK_COMPLETE,
    UPDATE_ROLLBACK_COMPLETE_CLEANUP_IN_PROGRESS,
    UPDATE_ROLLBACK_FAILED,
    UPDATE_ROLLBACK_IN_PROGRESS,
    "default"
}

Init == status = "default"
DoesNotExist(s) == s = "default"
IsCompleted(s) == s \in {CREATE_COMPLETE, DELETE_COMPLETE, ROLLBACK_COMPLETE, UPDATE_COMPLETE, UPDATE_ROLLBACK_COMPLETE}
IsFailed(s) == s \in {CREATE_FAILED, DELETE_FAILED, ROLLBACK_FAILED, UPDATE_ROLLBACK_FAILED}

(***************************************************************************)
(* Ongoing creation of one or more stacks.                                 *)
(***************************************************************************)
CreateInProgress == /\ DoesNotExist(status)
                    /\ status' = CREATE_IN_PROGRESS

(***************************************************************************)
(* Successful creation of one or more stacks.                              *)
(***************************************************************************)            
CreateComplete ==   /\ status = CREATE_IN_PROGRESS
                    /\ status' = CREATE_COMPLETE
 
(***************************************************************************)
(* Unsuccessful creation of one or more stacks.  View the stack events to  *)
(* see any associated error messages.  Possible reasons for a failed       *)
(* creation include insufficient permissions to work with all resources in *)
(* the stack, parameter values rejected by an AWS service, or a timeout    *)
(* during resource creation.                                               *)
(***************************************************************************)               
CreateFailed ==     /\ status = CREATE_IN_PROGRESS
                    /\ status' = CREATE_FAILED     

(***************************************************************************)
(* Ongoing removal of one or more stacks.                                  *)
(***************************************************************************)       
DeleteInProgress == /\ IsCompleted(status)
                      \/ IsFailed(status)
                    /\ status' = DELETE_IN_PROGRESS    

(***************************************************************************)
(* Successful deletion of one or more stacks.  Deleted stacks are retained *)
(* and viewable for 90 days.                                               *)
(***************************************************************************)             
DeleteComplete ==   /\ status = DELETE_IN_PROGRESS
                    /\ status' = DELETE_COMPLETE

(***************************************************************************)
(* Unsuccessful deletion of one or more stacks.  Because the delete        *)
(* failed, you might have some resources that are still running; however,  *)
(* you cannot work with or update the stack.  Delete the stack again or    *)
(* view the stack events to see any associated error messages.             *)
(***************************************************************************)  
DeleteFailed ==     /\ status = DELETE_IN_PROGRESS
                    /\ status' = DELETE_FAILED  
  
(***************************************************************************)
(* Ongoing update of one or more stacks.                                  *)
(***************************************************************************)    
UpdateInProgress == /\ IsCompleted(status)
                    /\ status' = UPDATE_IN_PROGRESS    
    
(***************************************************************************)
(* Successful update of one or more stacks.                                *)
(***************************************************************************)            
UpdateComplete ==   /\ status = UPDATE_IN_PROGRESS
                      \/ status = UPDATE_COMPLETE_CLEANUP_IN_PROGRESS
                    /\ status' = UPDATE_COMPLETE
                  
(***************************************************************************)
(* Ongoing removal of old resources for one or more stacks after a         *)
(* successful stack update.  For stack updates that require resources to   *)
(* be replaced, AWS CloudFormation creates the new resources first and     *)
(* then deletes the old resources to help reduce any interruptions with    *)
(* your stack.  In this state, the stack has been updated and is usable,   *)
(* but AWS CloudFormation is still deleting the old resources.             *)
(***************************************************************************)                            
UpdateCompleteCleanupInProgress == /\ status = UPDATE_IN_PROGRESS
                                   /\ status' = UPDATE_COMPLETE_CLEANUP_IN_PROGRESS                    
 
(***************************************************************************)
(* Ongoing removal of one or more stacks after a failed stack creation or  *)
(* after an explicitly cancelled stack creation.                           *)
(***************************************************************************) 
RollbackInProgress == /\ status = CREATE_IN_PROGRESS
                      /\ status' = ROLLBACK_IN_PROGRESS    

(***************************************************************************)
(* Successful removal of one or more stacks after a failed stack creation  *)
(* or after an explicitly canceled stack creation.  Any resources that     *)
(* were created during the create stack action are deleted.                *)
(*                                                                         *)
(* This status exists only after a failed stack creation.  It signifies    *)
(* that all operations from the partially created stack have been          *)
(* appropriately cleaned up.  When in this state, only a delete operation  *)
(* can be performed.                                                       *)
(***************************************************************************)   
RollbackComplete == /\ status = ROLLBACK_IN_PROGRESS
                    /\ status' = ROLLBACK_COMPLETE   
                    
(***************************************************************************)
(* Unsuccessful removal of one or more stacks after a failed stack         *)
(* creation or after an explicitly canceled stack creation.  Delete the    *)
(* stack or view the stack events to see any associated error messages.    *)
(***************************************************************************)                  
RollbackFailed == /\ status = ROLLBACK_IN_PROGRESS
                  /\ status' = ROLLBACK_FAILED 
                  
(***************************************************************************)
(* Ongoing return of one or more stacks to the previous working state      *)
(* after failed stack update.                                              *)
(***************************************************************************)
UpdateRollbackInProgress == /\ status = UPDATE_IN_PROGRESS
                            /\ status' = UPDATE_ROLLBACK_IN_PROGRESS                   
   
(***************************************************************************)
(* Successful return of one or more stacks to a previous working state     *)
(* after a failed stack update.                                            *)
(***************************************************************************)  
UpdateRollbackComplete == /\ status = UPDATE_ROLLBACK_IN_PROGRESS
                            \/ status = UPDATE_ROLLBACK_COMPLETE_CLEANUP_IN_PROGRESS
                          /\ status' = UPDATE_ROLLBACK_COMPLETE   
                     
(***************************************************************************)
(* Unsuccessful return of one or more stacks to a previous working state   *)
(* after a failed stack update.  When in this state, you can delete the    *)
(* stack or continue rollback.  You might need to fix errors before your   *)
(* stack can return to a working state.  Or, you can contact customer      *)
(* support to restore the stack to a usable state.                         *)
(***************************************************************************)
UpdateRollbackFailed == /\ status = UPDATE_ROLLBACK_IN_PROGRESS
                        /\ status' = UPDATE_ROLLBACK_FAILED   
   
  
(***************************************************************************)
(* This action simulates when an update rollback fails as a user must      *)
(* manually delete problematic resources before continuing an update       *)
(* rollback.                                                               *)
(***************************************************************************)
ManuallyDeleteResources == /\ status = UPDATE_ROLLBACK_FAILED
                           /\ status' = UPDATE_ROLLBACK_IN_PROGRESS  
  

(***************************************************************************)
(* Ongoing removal of new resources for one or more stacks after a failed  *)
(* stack update.  In this state, the stack has been rolled back to its     *)
(* previous working state and is usable, but AWS CloudFormation is still   *)
(* deleting any new resources it created during the stack update.          *)
(***************************************************************************)
UpdateRollbackCompleteCleanupInProgress == /\ status = UPDATE_ROLLBACK_IN_PROGRESS
                                           /\ status' = UPDATE_ROLLBACK_COMPLETE_CLEANUP_IN_PROGRESS

                         
(***************************************************************************)
(* Next state relation.                                                    *)
(***************************************************************************)
Next == \/ CreateInProgress
        \/ CreateComplete
        \/ CreateFailed
        \/ DeleteInProgress
        \/ DeleteComplete
        \/ DeleteFailed
        \/ UpdateInProgress
        \/ UpdateComplete
        \/ UpdateCompleteCleanupInProgress
        \/ RollbackInProgress
        \/ RollbackComplete
        \/ RollbackFailed
        \/ UpdateRollbackInProgress
        \/ UpdateRollbackComplete
        \/ UpdateRollbackFailed
        \/ ManuallyDeleteResources
        \/ UpdateRollbackCompleteCleanupInProgress
        
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sun May 19 18:18:58 PDT 2019 by jasondebolt
\* Created Sun May 19 15:44:54 PDT 2019 by jasondebolt
