--------------------------- MODULE py2lpp_validator_proofs ---------------------------
(*
 * L++ Blueprint: Artifact Validator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_validating, STATE_valid, STATE_invalid, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_valid
    /\ STATE_idle /= STATE_invalid
    /\ STATE_idle /= STATE_error
    /\ STATE_validating /= STATE_valid
    /\ STATE_validating /= STATE_invalid
    /\ STATE_validating /= STATE_error
    /\ STATE_valid /= STATE_invalid
    /\ STATE_valid /= STATE_error
    /\ STATE_invalid /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_validating, STATE_valid, STATE_invalid, STATE_error}
TerminalStates == {STATE_valid, STATE_invalid, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_validating

(* Transition: t_valid *)
t_t_valid ==
    /\ state = STATE_validating
    /\ state' = STATE_valid

(* Transition: t_invalid *)
t_t_invalid ==
    /\ state = STATE_validating
    /\ state' = STATE_invalid

(* Transition: t_error *)
t_t_error ==
    /\ state = STATE_validating
    /\ state' = STATE_error

Next ==
    \/ t_t_start
    \/ t_t_valid
    \/ t_t_invalid
    \/ t_t_error

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

LEMMA InvalidPreservesInv == Inv /\ t_t_invalid => Inv'
BY ConstantsDistinct DEF Inv, t_t_invalid, TypeInvariant, States

LEMMA ErrorPreservesInv == Inv /\ t_t_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_error, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, ValidPreservesInv, InvalidPreservesInv, ErrorPreservesInv DEF Next

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