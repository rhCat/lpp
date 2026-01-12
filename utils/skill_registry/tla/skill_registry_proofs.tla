--------------------------- MODULE skill_registry_proofs ---------------------------
(*
 * L++ Blueprint: Skill Registry
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_scanned, STATE_viewing, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_scanned
    /\ STATE_idle /= STATE_viewing
    /\ STATE_idle /= STATE_error
    /\ STATE_scanned /= STATE_viewing
    /\ STATE_scanned /= STATE_error
    /\ STATE_viewing /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_scanned, STATE_viewing, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_scan *)
t_t_scan ==
    /\ state = STATE_idle
    /\ state' = STATE_scanned

(* Transition: t_rescan *)
t_t_rescan ==
    /\ state = STATE_scanned
    /\ state' = STATE_scanned

(* Transition: t_select *)
t_t_select ==
    /\ state = STATE_scanned
    /\ state' = STATE_viewing

(* Transition: t_back *)
t_t_back ==
    /\ state = STATE_viewing
    /\ state' = STATE_scanned

(* Transition: t_select_another *)
t_t_select_another ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_scanned
    /\ state' = STATE_scanned

(* Transition: t_export_viewing *)
t_t_export_viewing ==
    /\ state = STATE_viewing
    /\ state' = STATE_viewing

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_scanned
    /\ state' = STATE_idle

(* Transition: t_retry *)
t_t_retry ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_error_from_idle *)
t_t_error_from_idle ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_error_from_scanned *)
t_t_error_from_scanned ==
    /\ state = STATE_scanned
    /\ state' = STATE_error

Next ==
    \/ t_t_scan
    \/ t_t_rescan
    \/ t_t_select
    \/ t_t_back
    \/ t_t_select_another
    \/ t_t_export
    \/ t_t_export_viewing
    \/ t_t_reset
    \/ t_t_retry
    \/ t_t_error_from_idle
    \/ t_t_error_from_scanned

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA ScanPreservesInv == Inv /\ t_t_scan => Inv'
BY ConstantsDistinct DEF Inv, t_t_scan, TypeInvariant, States

LEMMA RescanPreservesInv == Inv /\ t_t_rescan => Inv'
BY ConstantsDistinct DEF Inv, t_t_rescan, TypeInvariant, States

LEMMA SelectPreservesInv == Inv /\ t_t_select => Inv'
BY ConstantsDistinct DEF Inv, t_t_select, TypeInvariant, States

LEMMA BackPreservesInv == Inv /\ t_t_back => Inv'
BY ConstantsDistinct DEF Inv, t_t_back, TypeInvariant, States

LEMMA SelecanotherPreservesInv == Inv /\ t_t_select_another => Inv'
BY ConstantsDistinct DEF Inv, t_t_select_another, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA ExporviewingPreservesInv == Inv /\ t_t_export_viewing => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_viewing, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA RetryPreservesInv == Inv /\ t_t_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_retry, TypeInvariant, States

LEMMA ErrorFromIdlePreservesInv == Inv /\ t_t_error_from_idle => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_from_idle, TypeInvariant, States

LEMMA ErrorFromScannedPreservesInv == Inv /\ t_t_error_from_scanned => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_from_scanned, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY ScanPreservesInv, RescanPreservesInv, SelectPreservesInv, BackPreservesInv, SelecanotherPreservesInv, ExportPreservesInv, ExporviewingPreservesInv, ResetPreservesInv, RetryPreservesInv, ErrorFromIdlePreservesInv, ErrorFromScannedPreservesInv DEF Next

THEOREM InductiveInvariant == Inv /\ [Next]_vars => Inv'
BY NextPreservesInv, StutterPreservesInv DEF vars

THEOREM TypeSafety == Spec => []Inv
<1>1. Init => Inv
  BY InitEstablishesInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY InductiveInvariant
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================