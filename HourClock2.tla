----------------------------- MODULE HourClock2 -----------------------------

(***************************************************************************)
(* This module contains the definition of the specification HC2 from the   *)
(* Specifying Systems book.                                                *)
(***************************************************************************)

EXTENDS HourClock
(***************************************************************************)
(* This statement includes the current module, all the definitions and     *)
(* declarations from module HourClock, including the definitions of + and  *)
(* % from the Naturals module and the declaration of the variable hr.      *)
(***************************************************************************)

HCnxt2 == hr' = (hr % 12) + 1
HC2 == HCini /\ [][HCnxt2]_hr
-----------------------------------------------------------------------------
THEOREM HC <=> HC2

(***************************************************************************)
(* This theorem asserts that formulas HC and HC2 are equivalent.  The      *)
(* symbol <=>, which can also be typed as \equiv, is typeset as an         *)
(* equivalance symbol (a three-lined equals sign).                         *)
(***************************************************************************)


=============================================================================
\* Modification History
\* Last modified Thu May 16 13:07:22 PDT 2019 by jasondebolt
\* Created Thu May 16 13:03:14 PDT 2019 by jasondebolt
