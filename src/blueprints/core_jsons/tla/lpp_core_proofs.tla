--------------------------- MODULE lpp_core_proofs ---------------------------
(*
 * L++ Blueprint: L++ Core Atoms
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_evaluating, STATE_transitioning, STATE_mutating, STATE_dispatching, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_evaluating
    /\ STATE_idle /= STATE_transitioning
    /\ STATE_idle /= STATE_mutating
    /\ STATE_idle /= STATE_dispatching
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_evaluating /= STATE_transitioning
    /\ STATE_evaluating /= STATE_mutating
    /\ STATE_evaluating /= STATE_dispatching
    /\ STATE_evaluating /= STATE_complete
    /\ STATE_evaluating /= STATE_error
    /\ STATE_transitioning /= STATE_mutating
    /\ STATE_transitioning /= STATE_dispatching
    /\ STATE_transitioning /= STATE_complete
    /\ STATE_transitioning /= STATE_error
    /\ STATE_mutating /= STATE_dispatching
    /\ STATE_mutating /= STATE_complete
    /\ STATE_mutating /= STATE_error
    /\ STATE_dispatching /= STATE_complete
    /\ STATE_dispatching /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_evaluating, STATE_transitioning, STATE_mutating, STATE_dispatching, STATE_complete, STATE_error}
TerminalStates == {STATE_complete, STATE_error}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_evaluate *)
t_t_evaluate ==
    /\ state = STATE_idle
    /\ state' = STATE_evaluating

(* Transition: t_transition *)
t_t_transition ==
    /\ state = STATE_idle
    /\ state' = STATE_transitioning

(* Transition: t_mutate *)
t_t_mutate ==
    /\ state = STATE_idle
    /\ state' = STATE_mutating

(* Transition: t_dispatch *)
t_t_dispatch ==
    /\ state = STATE_idle
    /\ state' = STATE_dispatching

(* Transition: t_eval_done *)
t_t_eval_done ==
    /\ state = STATE_evaluating
    /\ state' = STATE_complete

(* Transition: t_trans_done *)
t_t_trans_done ==
    /\ state = STATE_transitioning
    /\ state' = STATE_complete

(* Transition: t_mutate_done *)
t_t_mutate_done ==
    /\ state = STATE_mutating
    /\ state' = STATE_complete

(* Transition: t_dispatch_done *)
t_t_dispatch_done ==
    /\ state = STATE_dispatching
    /\ state' = STATE_complete

(* Transition: t_eval_error *)
t_t_eval_error ==
    /\ state = STATE_evaluating
    /\ state' = STATE_error

(* Transition: t_trans_error *)
t_t_trans_error ==
    /\ state = STATE_transitioning
    /\ state' = STATE_error

(* Transition: t_mutate_error *)
t_t_mutate_error ==
    /\ state = STATE_mutating
    /\ state' = STATE_error

(* Transition: t_dispatch_error *)
t_t_dispatch_error ==
    /\ state = STATE_dispatching
    /\ state' = STATE_error

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_evaluate
    \/ t_t_transition
    \/ t_t_mutate
    \/ t_t_dispatch
    \/ t_t_eval_done
    \/ t_t_trans_done
    \/ t_t_mutate_done
    \/ t_t_dispatch_done
    \/ t_t_eval_error
    \/ t_t_trans_error
    \/ t_t_mutate_error
    \/ t_t_dispatch_error
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA EvaluatePreservesInv == Inv /\ t_t_evaluate => Inv'
BY ConstantsDistinct DEF Inv, t_t_evaluate, TypeInvariant, States

LEMMA TransitionPreservesInv == Inv /\ t_t_transition => Inv'
BY ConstantsDistinct DEF Inv, t_t_transition, TypeInvariant, States

LEMMA MutatePreservesInv == Inv /\ t_t_mutate => Inv'
BY ConstantsDistinct DEF Inv, t_t_mutate, TypeInvariant, States

LEMMA DispatchPreservesInv == Inv /\ t_t_dispatch => Inv'
BY ConstantsDistinct DEF Inv, t_t_dispatch, TypeInvariant, States

LEMMA EvalDonePreservesInv == Inv /\ t_t_eval_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_done, TypeInvariant, States

LEMMA TransDonePreservesInv == Inv /\ t_t_trans_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_trans_done, TypeInvariant, States

LEMMA MutateDonePreservesInv == Inv /\ t_t_mutate_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_mutate_done, TypeInvariant, States

LEMMA DispatchDonePreservesInv == Inv /\ t_t_dispatch_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_dispatch_done, TypeInvariant, States

LEMMA EvalErrorPreservesInv == Inv /\ t_t_eval_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_error, TypeInvariant, States

LEMMA TransErrorPreservesInv == Inv /\ t_t_trans_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_trans_error, TypeInvariant, States

LEMMA MutateErrorPreservesInv == Inv /\ t_t_mutate_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_mutate_error, TypeInvariant, States

LEMMA DispatchErrorPreservesInv == Inv /\ t_t_dispatch_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_dispatch_error, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY EvaluatePreservesInv, TransitionPreservesInv, MutatePreservesInv, DispatchPreservesInv, EvalDonePreservesInv, TransDonePreservesInv, MutateDonePreservesInv, DispatchDonePreservesInv, EvalErrorPreservesInv, TransErrorPreservesInv, MutateErrorPreservesInv, DispatchErrorPreservesInv, ResetPreservesInv DEF Next

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