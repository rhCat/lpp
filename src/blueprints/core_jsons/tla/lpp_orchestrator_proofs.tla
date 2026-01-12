--------------------------- MODULE lpp_orchestrator_proofs ---------------------------
(*
 * L++ Blueprint: L++ Orchestrator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_finding_transition, STATE_evaluating_gates, STATE_executing_actions, STATE_transitioning, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_finding_transition
    /\ STATE_idle /= STATE_evaluating_gates
    /\ STATE_idle /= STATE_executing_actions
    /\ STATE_idle /= STATE_transitioning
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_finding_transition /= STATE_evaluating_gates
    /\ STATE_finding_transition /= STATE_executing_actions
    /\ STATE_finding_transition /= STATE_transitioning
    /\ STATE_finding_transition /= STATE_complete
    /\ STATE_finding_transition /= STATE_error
    /\ STATE_evaluating_gates /= STATE_executing_actions
    /\ STATE_evaluating_gates /= STATE_transitioning
    /\ STATE_evaluating_gates /= STATE_complete
    /\ STATE_evaluating_gates /= STATE_error
    /\ STATE_executing_actions /= STATE_transitioning
    /\ STATE_executing_actions /= STATE_complete
    /\ STATE_executing_actions /= STATE_error
    /\ STATE_transitioning /= STATE_complete
    /\ STATE_transitioning /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_finding_transition, STATE_evaluating_gates, STATE_executing_actions, STATE_transitioning, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_dispatch *)
t_t_dispatch ==
    /\ state = STATE_idle
    /\ state' = STATE_finding_transition

(* Transition: t_found *)
t_t_found ==
    /\ state = STATE_finding_transition
    /\ state' = STATE_evaluating_gates

(* Transition: t_gates_pass *)
t_t_gates_pass ==
    /\ state = STATE_evaluating_gates
    /\ state' = STATE_executing_actions

(* Transition: t_actions_done *)
t_t_actions_done ==
    /\ state = STATE_executing_actions
    /\ state' = STATE_transitioning

(* Transition: t_transition_done *)
t_t_transition_done ==
    /\ state = STATE_transitioning
    /\ state' = STATE_complete

(* Transition: t_no_transition *)
t_t_no_transition ==
    /\ state = STATE_finding_transition
    /\ state' = STATE_error

(* Transition: t_gates_fail *)
t_t_gates_fail ==
    /\ state = STATE_evaluating_gates
    /\ state' = STATE_error

(* Transition: t_action_error *)
t_t_action_error ==
    /\ state = STATE_executing_actions
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_dispatch
    \/ t_t_found
    \/ t_t_gates_pass
    \/ t_t_actions_done
    \/ t_t_transition_done
    \/ t_t_no_transition
    \/ t_t_gates_fail
    \/ t_t_action_error
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA DispatchPreservesInv == Inv /\ t_t_dispatch => Inv'
BY ConstantsDistinct DEF Inv, t_t_dispatch, TypeInvariant, States

LEMMA FoundPreservesInv == Inv /\ t_t_found => Inv'
BY ConstantsDistinct DEF Inv, t_t_found, TypeInvariant, States

LEMMA GatesPassPreservesInv == Inv /\ t_t_gates_pass => Inv'
BY ConstantsDistinct DEF Inv, t_t_gates_pass, TypeInvariant, States

LEMMA ActionsDonePreservesInv == Inv /\ t_t_actions_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_actions_done, TypeInvariant, States

LEMMA TransitionDonePreservesInv == Inv /\ t_t_transition_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_transition_done, TypeInvariant, States

LEMMA NoTransitionPreservesInv == Inv /\ t_t_no_transition => Inv'
BY ConstantsDistinct DEF Inv, t_t_no_transition, TypeInvariant, States

LEMMA GatesFailPreservesInv == Inv /\ t_t_gates_fail => Inv'
BY ConstantsDistinct DEF Inv, t_t_gates_fail, TypeInvariant, States

LEMMA ActionErrorPreservesInv == Inv /\ t_t_action_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_action_error, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY DispatchPreservesInv, FoundPreservesInv, GatesPassPreservesInv, ActionsDonePreservesInv, TransitionDonePreservesInv, NoTransitionPreservesInv, GatesFailPreservesInv, ActionErrorPreservesInv, ResetPreservesInv DEF Next

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