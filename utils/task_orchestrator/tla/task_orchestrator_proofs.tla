--------------------------- MODULE task_orchestrator_proofs ---------------------------
(*
 * L++ Blueprint: Hierarchical Task Orchestrator
 * Version: 2.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_analyzing, STATE_expanding, STATE_planning, STATE_building, STATE_executing, STATE_traversing, STATE_reflecting, STATE_evaluating, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_expanding
    /\ STATE_idle /= STATE_planning
    /\ STATE_idle /= STATE_building
    /\ STATE_idle /= STATE_executing
    /\ STATE_idle /= STATE_traversing
    /\ STATE_idle /= STATE_reflecting
    /\ STATE_idle /= STATE_evaluating
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_analyzing /= STATE_expanding
    /\ STATE_analyzing /= STATE_planning
    /\ STATE_analyzing /= STATE_building
    /\ STATE_analyzing /= STATE_executing
    /\ STATE_analyzing /= STATE_traversing
    /\ STATE_analyzing /= STATE_reflecting
    /\ STATE_analyzing /= STATE_evaluating
    /\ STATE_analyzing /= STATE_complete
    /\ STATE_analyzing /= STATE_error
    /\ STATE_expanding /= STATE_planning
    /\ STATE_expanding /= STATE_building
    /\ STATE_expanding /= STATE_executing
    /\ STATE_expanding /= STATE_traversing
    /\ STATE_expanding /= STATE_reflecting
    /\ STATE_expanding /= STATE_evaluating
    /\ STATE_expanding /= STATE_complete
    /\ STATE_expanding /= STATE_error
    /\ STATE_planning /= STATE_building
    /\ STATE_planning /= STATE_executing
    /\ STATE_planning /= STATE_traversing
    /\ STATE_planning /= STATE_reflecting
    /\ STATE_planning /= STATE_evaluating
    /\ STATE_planning /= STATE_complete
    /\ STATE_planning /= STATE_error
    /\ STATE_building /= STATE_executing
    /\ STATE_building /= STATE_traversing
    /\ STATE_building /= STATE_reflecting
    /\ STATE_building /= STATE_evaluating
    /\ STATE_building /= STATE_complete
    /\ STATE_building /= STATE_error
    /\ STATE_executing /= STATE_traversing
    /\ STATE_executing /= STATE_reflecting
    /\ STATE_executing /= STATE_evaluating
    /\ STATE_executing /= STATE_complete
    /\ STATE_executing /= STATE_error
    /\ STATE_traversing /= STATE_reflecting
    /\ STATE_traversing /= STATE_evaluating
    /\ STATE_traversing /= STATE_complete
    /\ STATE_traversing /= STATE_error
    /\ STATE_reflecting /= STATE_evaluating
    /\ STATE_reflecting /= STATE_complete
    /\ STATE_reflecting /= STATE_error
    /\ STATE_evaluating /= STATE_complete
    /\ STATE_evaluating /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_analyzing, STATE_expanding, STATE_planning, STATE_building, STATE_executing, STATE_traversing, STATE_reflecting, STATE_evaluating, STATE_complete, STATE_error}
TerminalStates == {STATE_complete}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_start *)
t_t_start ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t_submit *)
t_t_submit ==
    /\ state = STATE_idle
    /\ state' = STATE_analyzing

(* Transition: t_ana_expand *)
t_t_ana_expand ==
    /\ state = STATE_analyzing
    /\ state' = STATE_expanding

(* Transition: t_ana_atomic *)
t_t_ana_atomic ==
    /\ state = STATE_analyzing
    /\ state' = STATE_planning

(* Transition: t_ana_err *)
t_t_ana_err ==
    /\ state = STATE_analyzing
    /\ state' = STATE_error

(* Transition: t_exp_more *)
t_t_exp_more ==
    /\ state = STATE_expanding
    /\ state' = STATE_expanding

(* Transition: t_exp_done *)
t_t_exp_done ==
    /\ state = STATE_expanding
    /\ state' = STATE_planning

(* Transition: t_exp_err *)
t_t_exp_err ==
    /\ state = STATE_expanding
    /\ state' = STATE_error

(* Transition: t_plan_build *)
t_t_plan_build ==
    /\ state = STATE_planning
    /\ state' = STATE_building

(* Transition: t_plan_exec *)
t_t_plan_exec ==
    /\ state = STATE_planning
    /\ state' = STATE_executing

(* Transition: t_plan_err *)
t_t_plan_err ==
    /\ state = STATE_planning
    /\ state' = STATE_error

(* Transition: t_bld_more *)
t_t_bld_more ==
    /\ state = STATE_building
    /\ state' = STATE_building

(* Transition: t_bld_done *)
t_t_bld_done ==
    /\ state = STATE_building
    /\ state' = STATE_executing

(* Transition: t_bld_err *)
t_t_bld_err ==
    /\ state = STATE_building
    /\ state' = STATE_error

(* Transition: t_exec_next *)
t_t_exec_next ==
    /\ state = STATE_executing
    /\ state' = STATE_traversing

(* Transition: t_exec_done *)
t_t_exec_done ==
    /\ state = STATE_executing
    /\ state' = STATE_reflecting

(* Transition: t_exec_err *)
t_t_exec_err ==
    /\ state = STATE_executing
    /\ state' = STATE_error

(* Transition: t_trav_build *)
t_t_trav_build ==
    /\ state = STATE_traversing
    /\ state' = STATE_building

(* Transition: t_trav_exec *)
t_t_trav_exec ==
    /\ state = STATE_traversing
    /\ state' = STATE_executing

(* Transition: t_trav_err *)
t_t_trav_err ==
    /\ state = STATE_traversing
    /\ state' = STATE_error

(* Transition: t_refl_ok *)
t_t_refl_ok ==
    /\ state = STATE_reflecting
    /\ state' = STATE_evaluating

(* Transition: t_refl_err *)
t_t_refl_err ==
    /\ state = STATE_reflecting
    /\ state' = STATE_error

(* Transition: t_eval_complete *)
t_t_eval_complete ==
    /\ state = STATE_evaluating
    /\ state' = STATE_complete

(* Transition: t_eval_continue *)
t_t_eval_continue ==
    /\ state = STATE_evaluating
    /\ state' = STATE_expanding

(* Transition: t_eval_max *)
t_t_eval_max ==
    /\ state = STATE_evaluating
    /\ state' = STATE_complete

(* Transition: t_eval_err *)
t_t_eval_err ==
    /\ state = STATE_evaluating
    /\ state' = STATE_error

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_reset *)
t_t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_idle

Next ==
    \/ t_t_start
    \/ t_t_submit
    \/ t_t_ana_expand
    \/ t_t_ana_atomic
    \/ t_t_ana_err
    \/ t_t_exp_more
    \/ t_t_exp_done
    \/ t_t_exp_err
    \/ t_t_plan_build
    \/ t_t_plan_exec
    \/ t_t_plan_err
    \/ t_t_bld_more
    \/ t_t_bld_done
    \/ t_t_bld_err
    \/ t_t_exec_next
    \/ t_t_exec_done
    \/ t_t_exec_err
    \/ t_t_trav_build
    \/ t_t_trav_exec
    \/ t_t_trav_err
    \/ t_t_refl_ok
    \/ t_t_refl_err
    \/ t_t_eval_complete
    \/ t_t_eval_continue
    \/ t_t_eval_max
    \/ t_t_eval_err
    \/ t_t_recover
    \/ t_t_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA StartPreservesInv == Inv /\ t_t_start => Inv'
BY ConstantsDistinct DEF Inv, t_t_start, TypeInvariant, States

LEMMA SubmitPreservesInv == Inv /\ t_t_submit => Inv'
BY ConstantsDistinct DEF Inv, t_t_submit, TypeInvariant, States

LEMMA AnaExpandPreservesInv == Inv /\ t_t_ana_expand => Inv'
BY ConstantsDistinct DEF Inv, t_t_ana_expand, TypeInvariant, States

LEMMA AnaAtomicPreservesInv == Inv /\ t_t_ana_atomic => Inv'
BY ConstantsDistinct DEF Inv, t_t_ana_atomic, TypeInvariant, States

LEMMA AnaErrPreservesInv == Inv /\ t_t_ana_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_ana_err, TypeInvariant, States

LEMMA ExpMorePreservesInv == Inv /\ t_t_exp_more => Inv'
BY ConstantsDistinct DEF Inv, t_t_exp_more, TypeInvariant, States

LEMMA ExpDonePreservesInv == Inv /\ t_t_exp_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_exp_done, TypeInvariant, States

LEMMA ExpErrPreservesInv == Inv /\ t_t_exp_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_exp_err, TypeInvariant, States

LEMMA PlanBuildPreservesInv == Inv /\ t_t_plan_build => Inv'
BY ConstantsDistinct DEF Inv, t_t_plan_build, TypeInvariant, States

LEMMA PlanExecPreservesInv == Inv /\ t_t_plan_exec => Inv'
BY ConstantsDistinct DEF Inv, t_t_plan_exec, TypeInvariant, States

LEMMA PlanErrPreservesInv == Inv /\ t_t_plan_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_plan_err, TypeInvariant, States

LEMMA BldMorePreservesInv == Inv /\ t_t_bld_more => Inv'
BY ConstantsDistinct DEF Inv, t_t_bld_more, TypeInvariant, States

LEMMA BldDonePreservesInv == Inv /\ t_t_bld_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_bld_done, TypeInvariant, States

LEMMA BldErrPreservesInv == Inv /\ t_t_bld_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_bld_err, TypeInvariant, States

LEMMA ExecNextPreservesInv == Inv /\ t_t_exec_next => Inv'
BY ConstantsDistinct DEF Inv, t_t_exec_next, TypeInvariant, States

LEMMA ExecDonePreservesInv == Inv /\ t_t_exec_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_exec_done, TypeInvariant, States

LEMMA ExecErrPreservesInv == Inv /\ t_t_exec_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_exec_err, TypeInvariant, States

LEMMA TravBuildPreservesInv == Inv /\ t_t_trav_build => Inv'
BY ConstantsDistinct DEF Inv, t_t_trav_build, TypeInvariant, States

LEMMA TravExecPreservesInv == Inv /\ t_t_trav_exec => Inv'
BY ConstantsDistinct DEF Inv, t_t_trav_exec, TypeInvariant, States

LEMMA TravErrPreservesInv == Inv /\ t_t_trav_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_trav_err, TypeInvariant, States

LEMMA ReflOkPreservesInv == Inv /\ t_t_refl_ok => Inv'
BY ConstantsDistinct DEF Inv, t_t_refl_ok, TypeInvariant, States

LEMMA ReflErrPreservesInv == Inv /\ t_t_refl_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_refl_err, TypeInvariant, States

LEMMA EvalCompletePreservesInv == Inv /\ t_t_eval_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_complete, TypeInvariant, States

LEMMA EvalContinuePreservesInv == Inv /\ t_t_eval_continue => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_continue, TypeInvariant, States

LEMMA EvalMaxPreservesInv == Inv /\ t_t_eval_max => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_max, TypeInvariant, States

LEMMA EvalErrPreservesInv == Inv /\ t_t_eval_err => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_err, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY StartPreservesInv, SubmitPreservesInv, AnaExpandPreservesInv, AnaAtomicPreservesInv, AnaErrPreservesInv, ExpMorePreservesInv, ExpDonePreservesInv, ExpErrPreservesInv, PlanBuildPreservesInv, PlanExecPreservesInv, PlanErrPreservesInv, BldMorePreservesInv, BldDonePreservesInv, BldErrPreservesInv, ExecNextPreservesInv, ExecDonePreservesInv, ExecErrPreservesInv, TravBuildPreservesInv, TravExecPreservesInv, TravErrPreservesInv, ReflOkPreservesInv, ReflErrPreservesInv, EvalCompletePreservesInv, EvalContinuePreservesInv, EvalMaxPreservesInv, EvalErrPreservesInv, RecoverPreservesInv, ResetPreservesInv DEF Next

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