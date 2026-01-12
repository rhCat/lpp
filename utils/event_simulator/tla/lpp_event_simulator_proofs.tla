--------------------------- MODULE lpp_event_simulator_proofs ---------------------------
(*
 * L++ Blueprint: L++ Event Sequence Simulator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_ready, STATE_simulating, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_ready
    /\ STATE_idle /= STATE_simulating
    /\ STATE_idle /= STATE_error
    /\ STATE_ready /= STATE_simulating
    /\ STATE_ready /= STATE_error
    /\ STATE_simulating /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_ready, STATE_simulating, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load *)
t_t_load ==
    /\ state = STATE_idle
    /\ state' = STATE_ready

(* Transition: t_load_error *)
t_t_load_error ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_reload *)
t_t_reload ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_reload_from_sim *)
t_t_reload_from_sim ==
    /\ state = STATE_simulating
    /\ state' = STATE_ready

(* Transition: t_start_simulation *)
t_t_start_simulation ==
    /\ state = STATE_ready
    /\ state' = STATE_simulating

(* Transition: t_dispatch *)
t_t_dispatch ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_set_context *)
t_t_set_context ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_refresh_events *)
t_t_refresh_events ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_evaluate_gates *)
t_t_evaluate_gates ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_fork *)
t_t_fork ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_switch_fork *)
t_t_switch_fork ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_step_back *)
t_t_step_back ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_set_sequence *)
t_t_set_sequence ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_run_sequence *)
t_t_run_sequence ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_fuzz *)
t_t_fuzz ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_find_path *)
t_t_find_path ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_explore *)
t_t_explore ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_view_trace *)
t_t_view_trace ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_view_space *)
t_t_view_space ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_import *)
t_t_import ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_simulating
    /\ state' = STATE_simulating

(* Transition: t_back_to_ready *)
t_t_back_to_ready ==
    /\ state = STATE_simulating
    /\ state' = STATE_ready

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_ready
    /\ state' = STATE_idle

(* Transition: t_unload_from_sim *)
t_t_unload_from_sim ==
    /\ state = STATE_simulating
    /\ state' = STATE_idle

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_load
    \/ t_t_load_error
    \/ t_t_reload
    \/ t_t_reload_from_sim
    \/ t_t_start_simulation
    \/ t_t_dispatch
    \/ t_t_set_context
    \/ t_t_refresh_events
    \/ t_t_evaluate_gates
    \/ t_t_fork
    \/ t_t_switch_fork
    \/ t_t_step_back
    \/ t_t_set_sequence
    \/ t_t_run_sequence
    \/ t_t_fuzz
    \/ t_t_find_path
    \/ t_t_explore
    \/ t_t_view_trace
    \/ t_t_view_space
    \/ t_t_export
    \/ t_t_import
    \/ t_t_reset
    \/ t_t_back_to_ready
    \/ t_t_unload
    \/ t_t_unload_from_sim
    \/ t_t_recover

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadPreservesInv == Inv /\ t_t_load => Inv'
BY ConstantsDistinct DEF Inv, t_t_load, TypeInvariant, States

LEMMA LoadErrorPreservesInv == Inv /\ t_t_load_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_error, TypeInvariant, States

LEMMA ReloadPreservesInv == Inv /\ t_t_reload => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload, TypeInvariant, States

LEMMA ReloadFromSimPreservesInv == Inv /\ t_t_reload_from_sim => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_sim, TypeInvariant, States

LEMMA StarsimulationPreservesInv == Inv /\ t_t_start_simulation => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_simulation, TypeInvariant, States

LEMMA DispatchPreservesInv == Inv /\ t_t_dispatch => Inv'
BY ConstantsDistinct DEF Inv, t_t_dispatch, TypeInvariant, States

LEMMA SecontextPreservesInv == Inv /\ t_t_set_context => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_context, TypeInvariant, States

LEMMA RefreshEventsPreservesInv == Inv /\ t_t_refresh_events => Inv'
BY ConstantsDistinct DEF Inv, t_t_refresh_events, TypeInvariant, States

LEMMA EvaluateGatesPreservesInv == Inv /\ t_t_evaluate_gates => Inv'
BY ConstantsDistinct DEF Inv, t_t_evaluate_gates, TypeInvariant, States

LEMMA ForkPreservesInv == Inv /\ t_t_fork => Inv'
BY ConstantsDistinct DEF Inv, t_t_fork, TypeInvariant, States

LEMMA SwitchForkPreservesInv == Inv /\ t_t_switch_fork => Inv'
BY ConstantsDistinct DEF Inv, t_t_switch_fork, TypeInvariant, States

LEMMA StepBackPreservesInv == Inv /\ t_t_step_back => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_back, TypeInvariant, States

LEMMA SesequencePreservesInv == Inv /\ t_t_set_sequence => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_sequence, TypeInvariant, States

LEMMA RunSequencePreservesInv == Inv /\ t_t_run_sequence => Inv'
BY ConstantsDistinct DEF Inv, t_t_run_sequence, TypeInvariant, States

LEMMA FuzzPreservesInv == Inv /\ t_t_fuzz => Inv'
BY ConstantsDistinct DEF Inv, t_t_fuzz, TypeInvariant, States

LEMMA FindPathPreservesInv == Inv /\ t_t_find_path => Inv'
BY ConstantsDistinct DEF Inv, t_t_find_path, TypeInvariant, States

LEMMA ExplorePreservesInv == Inv /\ t_t_explore => Inv'
BY ConstantsDistinct DEF Inv, t_t_explore, TypeInvariant, States

LEMMA ViewTracePreservesInv == Inv /\ t_t_view_trace => Inv'
BY ConstantsDistinct DEF Inv, t_t_view_trace, TypeInvariant, States

LEMMA ViewSpacePreservesInv == Inv /\ t_t_view_space => Inv'
BY ConstantsDistinct DEF Inv, t_t_view_space, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA ImportPreservesInv == Inv /\ t_t_import => Inv'
BY ConstantsDistinct DEF Inv, t_t_import, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA BackToReadyPreservesInv == Inv /\ t_t_back_to_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_ready, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadFromSimPreservesInv == Inv /\ t_t_unload_from_sim => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_sim, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, LoadErrorPreservesInv, ReloadPreservesInv, ReloadFromSimPreservesInv, StarsimulationPreservesInv, DispatchPreservesInv, SecontextPreservesInv, RefreshEventsPreservesInv, EvaluateGatesPreservesInv, ForkPreservesInv, SwitchForkPreservesInv, StepBackPreservesInv, SesequencePreservesInv, RunSequencePreservesInv, FuzzPreservesInv, FindPathPreservesInv, ExplorePreservesInv, ViewTracePreservesInv, ViewSpacePreservesInv, ExportPreservesInv, ImportPreservesInv, ResetPreservesInv, BackToReadyPreservesInv, UnloadPreservesInv, UnloadFromSimPreservesInv, RecoverPreservesInv DEF Next

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