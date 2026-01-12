--------------------------- MODULE lpp_schema_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Schema
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_querying, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_querying
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_querying /= STATE_complete
    /\ STATE_querying /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_querying, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_query_state *)
t_t_query_state ==
    /\ state = STATE_idle
    /\ state' = STATE_querying

(* Transition: t_query_transitions *)
t_t_query_transitions ==
    /\ state = STATE_idle
    /\ state' = STATE_querying

(* Transition: t_query_gate *)
t_t_query_gate ==
    /\ state = STATE_idle
    /\ state' = STATE_querying

(* Transition: t_query_action *)
t_t_query_action ==
    /\ state = STATE_idle
    /\ state' = STATE_querying

(* Transition: t_done *)
t_t_done ==
    /\ state = STATE_querying
    /\ state' = STATE_complete

(* Transition: t_err_not_found *)
t_t_err_not_found ==
    /\ state = STATE_querying
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_query_state
    \/ t_t_query_transitions
    \/ t_t_query_gate
    \/ t_t_query_action
    \/ t_t_done
    \/ t_t_err_not_found
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA QueryStatePreservesInv == Inv /\ t_t_query_state => Inv'
BY ConstantsDistinct DEF Inv, t_t_query_state, TypeInvariant, States

LEMMA QueryTransitionsPreservesInv == Inv /\ t_t_query_transitions => Inv'
BY ConstantsDistinct DEF Inv, t_t_query_transitions, TypeInvariant, States

LEMMA QueryGatePreservesInv == Inv /\ t_t_query_gate => Inv'
BY ConstantsDistinct DEF Inv, t_t_query_gate, TypeInvariant, States

LEMMA QueryActionPreservesInv == Inv /\ t_t_query_action => Inv'
BY ConstantsDistinct DEF Inv, t_t_query_action, TypeInvariant, States

LEMMA DonePreservesInv == Inv /\ t_t_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_done, TypeInvariant, States

LEMMA ErrNofoundPreservesInv == Inv /\ t_t_err_not_found => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_not_found, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY QueryStatePreservesInv, QueryTransitionsPreservesInv, QueryGatePreservesInv, QueryActionPreservesInv, DonePreservesInv, ErrNofoundPreservesInv, ResetPreservesInv DEF Next

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