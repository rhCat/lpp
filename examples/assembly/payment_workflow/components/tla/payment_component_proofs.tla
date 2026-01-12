--------------------------- MODULE payment_component_proofs ---------------------------
(*
 * L++ Blueprint: Payment Processing Component
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_validating, STATE_processing, STATE_payment_complete, STATE_payment_failed

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_processing
    /\ STATE_idle /= STATE_payment_complete
    /\ STATE_idle /= STATE_payment_failed
    /\ STATE_validating /= STATE_processing
    /\ STATE_validating /= STATE_payment_complete
    /\ STATE_validating /= STATE_payment_failed
    /\ STATE_processing /= STATE_payment_complete
    /\ STATE_processing /= STATE_payment_failed
    /\ STATE_payment_complete /= STATE_payment_failed

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_validating, STATE_processing, STATE_payment_complete, STATE_payment_failed}
TerminalStates == {STATE_payment_complete, STATE_payment_failed}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_validating

(* Transition: t_valid *)
t_t_valid ==
    /\ state = STATE_validating
    /\ state' = STATE_processing

(* Transition: t_invalid_token *)
t_t_invalid_token ==
    /\ state = STATE_validating
    /\ state' = STATE_payment_failed

(* Transition: t_invalid_amount *)
t_t_invalid_amount ==
    /\ state = STATE_validating
    /\ state' = STATE_payment_failed

(* Transition: t_success *)
t_t_success ==
    /\ state = STATE_processing
    /\ state' = STATE_payment_complete

(* Transition: t_process_fail *)
t_t_process_fail ==
    /\ state = STATE_processing
    /\ state' = STATE_payment_failed

Next ==
    \/ t_t_start
    \/ t_t_valid
    \/ t_t_invalid_token
    \/ t_t_invalid_amount
    \/ t_t_success
    \/ t_t_process_fail

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA ValidPreservesInv == Inv /\ t_t_valid => Inv'
BY ConstantsDistinct DEF Inv, t_t_valid, TypeInvariant, States

LEMMA InvalidTokenPreservesInv == Inv /\ t_t_invalid_token => Inv'
BY ConstantsDistinct DEF Inv, t_t_invalid_token, TypeInvariant, States

LEMMA InvalidAmountPreservesInv == Inv /\ t_t_invalid_amount => Inv'
BY ConstantsDistinct DEF Inv, t_t_invalid_amount, TypeInvariant, States

LEMMA SuccessPreservesInv == Inv /\ t_t_success => Inv'
BY ConstantsDistinct DEF Inv, t_t_success, TypeInvariant, States

LEMMA ProcessFailPreservesInv == Inv /\ t_t_process_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_process_fail, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, ValidPreservesInv, InvalidTokenPreservesInv, InvalidAmountPreservesInv, SuccessPreservesInv, ProcessFailPreservesInv DEF Next

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