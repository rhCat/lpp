--------------------------- MODULE auth_component_proofs ---------------------------
(*
 * L++ Blueprint: Authentication Component
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_validating, STATE_authenticated, STATE_auth_failed

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_authenticated
    /\ STATE_idle /= STATE_auth_failed
    /\ STATE_validating /= STATE_authenticated
    /\ STATE_validating /= STATE_auth_failed
    /\ STATE_authenticated /= STATE_auth_failed

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_validating, STATE_authenticated, STATE_auth_failed}
TerminalStates == {STATE_authenticated, STATE_auth_failed}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_submit *)
t_t_submit ==
    /\ state = STATE_idle
    /\ state' = STATE_validating

(* Transition: t_valid *)
t_t_valid ==
    /\ state = STATE_validating
    /\ state' = STATE_authenticated

(* Transition: t_invalid *)
t_t_invalid ==
    /\ state = STATE_validating
    /\ state' = STATE_auth_failed

Next ==
    \/ t_t_submit
    \/ t_t_valid
    \/ t_t_invalid

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA SubmitPreservesInv == Inv /\ t_t_submit => Inv'
BY ConstantsDistinct DEF Inv, t_t_submit, TypeInvariant, States

LEMMA ValidPreservesInv == Inv /\ t_t_valid => Inv'
BY ConstantsDistinct DEF Inv, t_t_valid, TypeInvariant, States

LEMMA InvalidPreservesInv == Inv /\ t_t_invalid => Inv'
BY ConstantsDistinct DEF Inv, t_t_invalid, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY SubmitPreservesInv, ValidPreservesInv, InvalidPreservesInv DEF Next

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