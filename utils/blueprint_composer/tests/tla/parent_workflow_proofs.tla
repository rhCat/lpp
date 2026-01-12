--------------------------- MODULE parent_workflow_proofs ---------------------------
(*
 * L++ Blueprint: Parent Workflow
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_validating, STATE_processing, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_processing
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_validating /= STATE_processing
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_processing /= STATE_complete
    /\ STATE_processing /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_validating, STATE_processing, STATE_complete, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_submit *)
t_t_submit ==
    /\ state = STATE_idle
    /\ state' = STATE_validating

(* Transition: t_validated *)
t_t_validated ==
    /\ state = STATE_validating
    /\ state' = STATE_processing

(* Transition: t_validation_failed *)
t_t_validation_failed ==
    /\ state = STATE_validating
    /\ state' = STATE_error

(* Transition: t_process_complete *)
t_t_process_complete ==
    /\ state = STATE_processing
    /\ state' = STATE_complete

(* Transition: t_process_error *)
t_t_process_error ==
    /\ state = STATE_processing
    /\ state' = STATE_error

(* Transition: t_reset_from_complete *)
t_t_reset_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

(* Transition: t_reset_from_error *)
t_t_reset_from_error ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_retry *)
t_t_retry ==
    /\ state = STATE_error
    /\ state' = STATE_validating

Next ==
    \/ t_t_submit
    \/ t_t_validated
    \/ t_t_validation_failed
    \/ t_t_process_complete
    \/ t_t_process_error
    \/ t_t_reset_from_complete
    \/ t_t_reset_from_error
    \/ t_t_retry

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA SubmitPreservesInv == Inv /\ t_t_submit => Inv'
BY ConstantsDistinct DEF Inv, t_t_submit, TypeInvariant, States

LEMMA ValidatedPreservesInv == Inv /\ t_t_validated => Inv'
BY ConstantsDistinct DEF Inv, t_t_validated, TypeInvariant, States

LEMMA ValidationFailedPreservesInv == Inv /\ t_t_validation_failed => Inv'
BY ConstantsDistinct DEF Inv, t_t_validation_failed, TypeInvariant, States

LEMMA ProcessCompletePreservesInv == Inv /\ t_t_process_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_process_complete, TypeInvariant, States

LEMMA ProcessErrorPreservesInv == Inv /\ t_t_process_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_process_error, TypeInvariant, States

LEMMA ResefromCompletePreservesInv == Inv /\ t_t_reset_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_from_complete, TypeInvariant, States

LEMMA ResefromErrorPreservesInv == Inv /\ t_t_reset_from_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_from_error, TypeInvariant, States

LEMMA RetryPreservesInv == Inv /\ t_t_retry => Inv'
BY ConstantsDistinct DEF Inv, t_t_retry, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY SubmitPreservesInv, ValidatedPreservesInv, ValidationFailedPreservesInv, ProcessCompletePreservesInv, ProcessErrorPreservesInv, ResefromCompletePreservesInv, ResefromErrorPreservesInv, RetryPreservesInv DEF Next

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