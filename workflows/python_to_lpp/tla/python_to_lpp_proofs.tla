--------------------------- MODULE python_to_lpp_proofs ---------------------------
(*
 * L++ Blueprint: Python to L++ Refactorer
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_scanning, STATE_analyzing, STATE_extracting, STATE_generating_blueprints, STATE_generating_compute, STATE_generating_docs, STATE_validating, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_scanning
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_extracting
    /\ STATE_idle /= STATE_generating_blueprints
    /\ STATE_idle /= STATE_generating_compute
    /\ STATE_idle /= STATE_generating_docs
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_scanning /= STATE_analyzing
    /\ STATE_scanning /= STATE_extracting
    /\ STATE_scanning /= STATE_generating_blueprints
    /\ STATE_scanning /= STATE_generating_compute
    /\ STATE_scanning /= STATE_generating_docs
    /\ STATE_scanning /= STATE_validating
    /\ STATE_scanning /= STATE_complete
    /\ STATE_scanning /= STATE_error
    /\ STATE_analyzing /= STATE_extracting
    /\ STATE_analyzing /= STATE_generating_blueprints
    /\ STATE_analyzing /= STATE_generating_compute
    /\ STATE_analyzing /= STATE_generating_docs
    /\ STATE_analyzing /= STATE_validating
    /\ STATE_analyzing /= STATE_complete
    /\ STATE_analyzing /= STATE_error
    /\ STATE_extracting /= STATE_generating_blueprints
    /\ STATE_extracting /= STATE_generating_compute
    /\ STATE_extracting /= STATE_generating_docs
    /\ STATE_extracting /= STATE_validating
    /\ STATE_extracting /= STATE_complete
    /\ STATE_extracting /= STATE_error
    /\ STATE_generating_blueprints /= STATE_generating_compute
    /\ STATE_generating_blueprints /= STATE_generating_docs
    /\ STATE_generating_blueprints /= STATE_validating
    /\ STATE_generating_blueprints /= STATE_complete
    /\ STATE_generating_blueprints /= STATE_error
    /\ STATE_generating_compute /= STATE_generating_docs
    /\ STATE_generating_compute /= STATE_validating
    /\ STATE_generating_compute /= STATE_complete
    /\ STATE_generating_compute /= STATE_error
    /\ STATE_generating_docs /= STATE_validating
    /\ STATE_generating_docs /= STATE_complete
    /\ STATE_generating_docs /= STATE_error
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_scanning, STATE_analyzing, STATE_extracting, STATE_generating_blueprints, STATE_generating_compute, STATE_generating_docs, STATE_validating, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t0 *)
t_t0 ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t1 *)
t_t1 ==
    /\ state = STATE_idle
    /\ state' = STATE_scanning

(* Transition: t2 *)
t_t2 ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t3 *)
t_t3 ==
    /\ state = STATE_scanning
    /\ state' = STATE_analyzing

(* Transition: t4 *)
t_t4 ==
    /\ state = STATE_scanning
    /\ state' = STATE_error

(* Transition: t5 *)
t_t5 ==
    /\ state = STATE_analyzing
    /\ state' = STATE_extracting

(* Transition: t6 *)
t_t6 ==
    /\ state = STATE_extracting
    /\ state' = STATE_generating_blueprints

(* Transition: t7 *)
t_t7 ==
    /\ state = STATE_generating_blueprints
    /\ state' = STATE_generating_compute

(* Transition: t8 *)
t_t8 ==
    /\ state = STATE_generating_compute
    /\ state' = STATE_generating_docs

(* Transition: t9 *)
t_t9 ==
    /\ state = STATE_generating_compute
    /\ state' = STATE_validating

(* Transition: t10 *)
t_t10 ==
    /\ state = STATE_generating_docs
    /\ state' = STATE_validating

(* Transition: t11 *)
t_t11 ==
    /\ state = STATE_validating
    /\ state' = STATE_complete

(* Transition: t12 *)
t_t12 ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

(* Transition: t13 *)
t_t13 ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t14 *)
t_t14 ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

Next ==
    \/ t_t0
    \/ t_t1
    \/ t_t2
    \/ t_t3
    \/ t_t4
    \/ t_t5
    \/ t_t6
    \/ t_t7
    \/ t_t8
    \/ t_t9
    \/ t_t10
    \/ t_t11
    \/ t_t12
    \/ t_t13
    \/ t_t14

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

LEMMA T4PreservesInv == Inv /\ t_t4 => Inv'
BY ConstantsDistinct DEF Inv, t_t4, TypeInvariant, States

LEMMA T5PreservesInv == Inv /\ t_t5 => Inv'
BY ConstantsDistinct DEF Inv, t_t5, TypeInvariant, States

LEMMA T6PreservesInv == Inv /\ t_t6 => Inv'
BY ConstantsDistinct DEF Inv, t_t6, TypeInvariant, States

LEMMA T7PreservesInv == Inv /\ t_t7 => Inv'
BY ConstantsDistinct DEF Inv, t_t7, TypeInvariant, States

LEMMA T8PreservesInv == Inv /\ t_t8 => Inv'
BY ConstantsDistinct DEF Inv, t_t8, TypeInvariant, States

LEMMA T9PreservesInv == Inv /\ t_t9 => Inv'
BY ConstantsDistinct DEF Inv, t_t9, TypeInvariant, States

LEMMA T10PreservesInv == Inv /\ t_t10 => Inv'
BY ConstantsDistinct DEF Inv, t_t10, TypeInvariant, States

LEMMA T11PreservesInv == Inv /\ t_t11 => Inv'
BY ConstantsDistinct DEF Inv, t_t11, TypeInvariant, States

LEMMA T12PreservesInv == Inv /\ t_t12 => Inv'
BY ConstantsDistinct DEF Inv, t_t12, TypeInvariant, States

LEMMA T13PreservesInv == Inv /\ t_t13 => Inv'
BY ConstantsDistinct DEF Inv, t_t13, TypeInvariant, States

LEMMA T14PreservesInv == Inv /\ t_t14 => Inv'
BY ConstantsDistinct DEF Inv, t_t14, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY T0PreservesInv, T1PreservesInv, T2PreservesInv, T3PreservesInv, T4PreservesInv, T5PreservesInv, T6PreservesInv, T7PreservesInv, T8PreservesInv, T9PreservesInv, T10PreservesInv, T11PreservesInv, T12PreservesInv, T13PreservesInv, T14PreservesInv DEF Next

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