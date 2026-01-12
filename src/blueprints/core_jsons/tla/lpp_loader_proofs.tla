--------------------------- MODULE lpp_loader_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Loader
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_reading, STATE_validating, STATE_loading, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_reading
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_loading
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_reading /= STATE_validating
    /\ STATE_reading /= STATE_loading
    /\ STATE_reading /= STATE_complete
    /\ STATE_reading /= STATE_error
    /\ STATE_validating /= STATE_loading
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_loading /= STATE_complete
    /\ STATE_loading /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_reading, STATE_validating, STATE_loading, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t0 *)
t_t0 ==
    /\ state = STATE_idle
    /\ state' = STATE_reading

(* Transition: t1 *)
t_t1 ==
    /\ state = STATE_reading
    /\ state' = STATE_validating

(* Transition: t2 *)
t_t2 ==
    /\ state = STATE_validating
    /\ state' = STATE_loading

(* Transition: t3 *)
t_t3 ==
    /\ state = STATE_loading
    /\ state' = STATE_complete

(* Transition: t_err_read *)
t_t_err_read ==
    /\ state = STATE_reading
    /\ state' = STATE_error

(* Transition: t_err_validate *)
t_t_err_validate ==
    /\ state = STATE_validating
    /\ state' = STATE_error

(* Transition: t_err_load *)
t_t_err_load ==
    /\ state = STATE_loading
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t0
    \/ t_t1
    \/ t_t2
    \/ t_t3
    \/ t_t_err_read
    \/ t_t_err_validate
    \/ t_t_err_load
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA T0PreservesInv == Inv /\ t_t0 => Inv'
BY ConstantsDistinct DEF Inv, t_t0, TypeInvariant, States

LEMMA T1PreservesInv == Inv /\ t_t1 => Inv'
BY ConstantsDistinct DEF Inv, t_t1, TypeInvariant, States

LEMMA T2PreservesInv == Inv /\ t_t2 => Inv'
BY ConstantsDistinct DEF Inv, t_t2, TypeInvariant, States

LEMMA T3PreservesInv == Inv /\ t_t3 => Inv'
BY ConstantsDistinct DEF Inv, t_t3, TypeInvariant, States

LEMMA ErrReadPreservesInv == Inv /\ t_t_err_read => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_read, TypeInvariant, States

LEMMA ErrValidatePreservesInv == Inv /\ t_t_err_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_validate, TypeInvariant, States

LEMMA ErrLoadPreservesInv == Inv /\ t_t_err_load => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_load, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY T0PreservesInv, T1PreservesInv, T2PreservesInv, T3PreservesInv, ErrReadPreservesInv, ErrValidatePreservesInv, ErrLoadPreservesInv, ResetPreservesInv DEF Next

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