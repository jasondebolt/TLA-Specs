------------------------------ MODULE Assumes ------------------------------

(* You can run this as a model using "No behavior spec" mode *)
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
  


=============================================================================
\* Modification History
\* Last modified Sat Apr 20 20:07:41 PDT 2019 by jasondebolt
\* Created Sat Apr 20 20:01:34 PDT 2019 by jasondebolt
