--------------------------- MODULE audit_component_proofs ---------------------------
(*
 * L++ Blueprint: Audit Logging Component
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_logging, STATE_logged

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_logging
    /\ STATE_idle /= STATE_logged
    /\ STATE_logging /= STATE_logged

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_logging, STATE_logged}
TerminalStates == {STATE_logged}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_log *)
t_t_log ==
    /\ state = STATE_idle
    /\ state' = STATE_logging

(* Transition: t_complete *)
t_t_complete ==
    /\ state = STATE_logging
    /\ state' = STATE_logged

Next ==
    \/ t_t_log
    \/ t_t_complete

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LogPreservesInv == Inv /\ t_t_log => Inv'
BY ConstantsDistinct DEF Inv, t_t_log, TypeInvariant, States

LEMMA CompletePreservesInv == Inv /\ t_t_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_complete, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LogPreservesInv, CompletePreservesInv DEF Next

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