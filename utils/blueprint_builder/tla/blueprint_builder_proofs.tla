--------------------------- MODULE blueprint_builder_proofs ---------------------------
(*
 * L++ Blueprint: Blueprint Builder
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_building, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_building
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_building /= STATE_complete
    /\ STATE_building /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_building, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t0 *)
t_t0 ==
    /\ state = STATE_idle
    /\ state' = STATE_building

(* Transition: t1 *)
t_t1 ==
    /\ state = STATE_building
    /\ state' = STATE_complete

(* Transition: t2 *)
t_t2 ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

Next ==
    \/ t_t0
    \/ t_t1
    \/ t_t2

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

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY T0PreservesInv, T1PreservesInv, T2PreservesInv DEF Next

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