--------------------------- MODULE lpp_validator_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Validator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_checking_structure, STATE_checking_states, STATE_checking_transitions, STATE_checking_gates, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_checking_structure
    /\ STATE_idle /= STATE_checking_states
    /\ STATE_idle /= STATE_checking_transitions
    /\ STATE_idle /= STATE_checking_gates
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_checking_structure /= STATE_checking_states
    /\ STATE_checking_structure /= STATE_checking_transitions
    /\ STATE_checking_structure /= STATE_checking_gates
    /\ STATE_checking_structure /= STATE_complete
    /\ STATE_checking_structure /= STATE_error
    /\ STATE_checking_states /= STATE_checking_transitions
    /\ STATE_checking_states /= STATE_checking_gates
    /\ STATE_checking_states /= STATE_complete
    /\ STATE_checking_states /= STATE_error
    /\ STATE_checking_transitions /= STATE_checking_gates
    /\ STATE_checking_transitions /= STATE_complete
    /\ STATE_checking_transitions /= STATE_error
    /\ STATE_checking_gates /= STATE_complete
    /\ STATE_checking_gates /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_checking_structure, STATE_checking_states, STATE_checking_transitions, STATE_checking_gates, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_checking_structure

(* Transition: t_structure_ok *)
t_t_structure_ok ==
    /\ state = STATE_checking_structure
    /\ state' = STATE_checking_states

(* Transition: t_states_ok *)
t_t_states_ok ==
    /\ state = STATE_checking_states
    /\ state' = STATE_checking_transitions

(* Transition: t_transitions_ok *)
t_t_transitions_ok ==
    /\ state = STATE_checking_transitions
    /\ state' = STATE_checking_gates

(* Transition: t_gates_ok *)
t_t_gates_ok ==
    /\ state = STATE_checking_gates
    /\ state' = STATE_complete

(* Transition: t_err_structure *)
t_t_err_structure ==
    /\ state = STATE_checking_structure
    /\ state' = STATE_error

(* Transition: t_err_states *)
t_t_err_states ==
    /\ state = STATE_checking_states
    /\ state' = STATE_error

(* Transition: t_err_transitions *)
t_t_err_transitions ==
    /\ state = STATE_checking_transitions
    /\ state' = STATE_error

(* Transition: t_err_gates *)
t_t_err_gates ==
    /\ state = STATE_checking_gates
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_start
    \/ t_t_structure_ok
    \/ t_t_states_ok
    \/ t_t_transitions_ok
    \/ t_t_gates_ok
    \/ t_t_err_structure
    \/ t_t_err_states
    \/ t_t_err_transitions
    \/ t_t_err_gates
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA StructureOkPreservesInv == Inv /\ t_t_structure_ok => Inv'
BY ConstantsDistinct DEF Inv, t_t_structure_ok, TypeInvariant, States

LEMMA StatesOkPreservesInv == Inv /\ t_t_states_ok => Inv'
BY ConstantsDistinct DEF Inv, t_t_states_ok, TypeInvariant, States

LEMMA TransitionsOkPreservesInv == Inv /\ t_t_transitions_ok => Inv'
BY ConstantsDistinct DEF Inv, t_t_transitions_ok, TypeInvariant, States

LEMMA GatesOkPreservesInv == Inv /\ t_t_gates_ok => Inv'
BY ConstantsDistinct DEF Inv, t_t_gates_ok, TypeInvariant, States

LEMMA ErrStructurePreservesInv == Inv /\ t_t_err_structure => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_structure, TypeInvariant, States

LEMMA ErrStatesPreservesInv == Inv /\ t_t_err_states => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_states, TypeInvariant, States

LEMMA ErrTransitionsPreservesInv == Inv /\ t_t_err_transitions => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_transitions, TypeInvariant, States

LEMMA ErrGatesPreservesInv == Inv /\ t_t_err_gates => Inv'
BY ConstantsDistinct DEF Inv, t_t_err_gates, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, StructureOkPreservesInv, StatesOkPreservesInv, TransitionsOkPreservesInv, GatesOkPreservesInv, ErrStructurePreservesInv, ErrStatesPreservesInv, ErrTransitionsPreservesInv, ErrGatesPreservesInv, ResetPreservesInv DEF Next

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