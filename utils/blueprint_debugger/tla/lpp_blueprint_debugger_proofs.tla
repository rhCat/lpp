--------------------------- MODULE lpp_blueprint_debugger_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Debugger
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loaded, STATE_debugging, STATE_paused, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loaded
    /\ STATE_idle /= STATE_debugging
    /\ STATE_idle /= STATE_paused
    /\ STATE_idle /= STATE_error
    /\ STATE_loaded /= STATE_debugging
    /\ STATE_loaded /= STATE_paused
    /\ STATE_loaded /= STATE_error
    /\ STATE_debugging /= STATE_paused
    /\ STATE_debugging /= STATE_error
    /\ STATE_paused /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loaded, STATE_debugging, STATE_paused, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load *)
t_t_load ==
    /\ state = STATE_idle
    /\ state' = STATE_loaded

(* Transition: t_load_error *)
t_t_load_error ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_reload *)
t_t_reload ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_reload_from_debug *)
t_t_reload_from_debug ==
    /\ state = STATE_debugging
    /\ state' = STATE_loaded

(* Transition: t_start_debug *)
t_t_start_debug ==
    /\ state = STATE_loaded
    /\ state' = STATE_debugging

(* Transition: t_set_bp_loaded *)
t_t_set_bp_loaded ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_set_bp_debug *)
t_t_set_bp_debug ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_set_bp_paused *)
t_t_set_bp_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_remove_bp_debug *)
t_t_remove_bp_debug ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_remove_bp_paused *)
t_t_remove_bp_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_list_bp_debug *)
t_t_list_bp_debug ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_list_bp_paused *)
t_t_list_bp_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_step *)
t_t_step ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_step_to_paused *)
t_t_step_to_paused ==
    /\ state = STATE_debugging
    /\ state' = STATE_paused

(* Transition: t_step_over *)
t_t_step_over ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_step_back *)
t_t_step_back ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_step_back_paused *)
t_t_step_back_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_debugging

(* Transition: t_run *)
t_t_run ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_run_hit_bp *)
t_t_run_hit_bp ==
    /\ state = STATE_debugging
    /\ state' = STATE_paused

(* Transition: t_continue *)
t_t_continue ==
    /\ state = STATE_paused
    /\ state' = STATE_debugging

(* Transition: t_continue_run *)
t_t_continue_run ==
    /\ state = STATE_paused
    /\ state' = STATE_debugging

(* Transition: t_pause *)
t_t_pause ==
    /\ state = STATE_debugging
    /\ state' = STATE_paused

(* Transition: t_stop *)
t_t_stop ==
    /\ state = STATE_debugging
    /\ state' = STATE_loaded

(* Transition: t_stop_paused *)
t_t_stop_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_loaded

(* Transition: t_inspect_state *)
t_t_inspect_state ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_inspect_state_paused *)
t_t_inspect_state_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_inspect_context *)
t_t_inspect_context ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_inspect_context_paused *)
t_t_inspect_context_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_eval *)
t_t_eval ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_eval_paused *)
t_t_eval_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_add_watch *)
t_t_add_watch ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_add_watch_paused *)
t_t_add_watch_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_remove_watch *)
t_t_remove_watch ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_get_watches *)
t_t_get_watches ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_get_watches_paused *)
t_t_get_watches_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_history *)
t_t_history ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_history_paused *)
t_t_history_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_goto_step *)
t_t_goto_step ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_goto_step_paused *)
t_t_goto_step_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_debugging

(* Transition: t_compare *)
t_t_compare ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_compare_paused *)
t_t_compare_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_reset_paused *)
t_t_reset_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_debugging

(* Transition: t_status *)
t_t_status ==
    /\ state = STATE_debugging
    /\ state' = STATE_debugging

(* Transition: t_status_paused *)
t_t_status_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_loaded
    /\ state' = STATE_idle

(* Transition: t_unload_debug *)
t_t_unload_debug ==
    /\ state = STATE_debugging
    /\ state' = STATE_idle

(* Transition: t_unload_paused *)
t_t_unload_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_idle

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_load
    \/ t_t_load_error
    \/ t_t_reload
    \/ t_t_reload_from_debug
    \/ t_t_start_debug
    \/ t_t_set_bp_loaded
    \/ t_t_set_bp_debug
    \/ t_t_set_bp_paused
    \/ t_t_remove_bp_debug
    \/ t_t_remove_bp_paused
    \/ t_t_list_bp_debug
    \/ t_t_list_bp_paused
    \/ t_t_step
    \/ t_t_step_to_paused
    \/ t_t_step_over
    \/ t_t_step_back
    \/ t_t_step_back_paused
    \/ t_t_run
    \/ t_t_run_hit_bp
    \/ t_t_continue
    \/ t_t_continue_run
    \/ t_t_pause
    \/ t_t_stop
    \/ t_t_stop_paused
    \/ t_t_inspect_state
    \/ t_t_inspect_state_paused
    \/ t_t_inspect_context
    \/ t_t_inspect_context_paused
    \/ t_t_eval
    \/ t_t_eval_paused
    \/ t_t_add_watch
    \/ t_t_add_watch_paused
    \/ t_t_remove_watch
    \/ t_t_get_watches
    \/ t_t_get_watches_paused
    \/ t_t_history
    \/ t_t_history_paused
    \/ t_t_goto_step
    \/ t_t_goto_step_paused
    \/ t_t_compare
    \/ t_t_compare_paused
    \/ t_t_reset
    \/ t_t_reset_paused
    \/ t_t_status
    \/ t_t_status_paused
    \/ t_t_unload
    \/ t_t_unload_debug
    \/ t_t_unload_paused
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

LEMMA ReloadFromDebugPreservesInv == Inv /\ t_t_reload_from_debug => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_debug, TypeInvariant, States

LEMMA StardebugPreservesInv == Inv /\ t_t_start_debug => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_debug, TypeInvariant, States

LEMMA SebpLoadedPreservesInv == Inv /\ t_t_set_bp_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_bp_loaded, TypeInvariant, States

LEMMA SebpDebugPreservesInv == Inv /\ t_t_set_bp_debug => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_bp_debug, TypeInvariant, States

LEMMA SebpPausedPreservesInv == Inv /\ t_t_set_bp_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_bp_paused, TypeInvariant, States

LEMMA RemoveBpDebugPreservesInv == Inv /\ t_t_remove_bp_debug => Inv'
BY ConstantsDistinct DEF Inv, t_t_remove_bp_debug, TypeInvariant, States

LEMMA RemoveBpPausedPreservesInv == Inv /\ t_t_remove_bp_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_remove_bp_paused, TypeInvariant, States

LEMMA LisbpDebugPreservesInv == Inv /\ t_t_list_bp_debug => Inv'
BY ConstantsDistinct DEF Inv, t_t_list_bp_debug, TypeInvariant, States

LEMMA LisbpPausedPreservesInv == Inv /\ t_t_list_bp_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_list_bp_paused, TypeInvariant, States

LEMMA StepPreservesInv == Inv /\ t_t_step => Inv'
BY ConstantsDistinct DEF Inv, t_t_step, TypeInvariant, States

LEMMA StepToPausedPreservesInv == Inv /\ t_t_step_to_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_to_paused, TypeInvariant, States

LEMMA StepOverPreservesInv == Inv /\ t_t_step_over => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_over, TypeInvariant, States

LEMMA StepBackPreservesInv == Inv /\ t_t_step_back => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_back, TypeInvariant, States

LEMMA StepBackPausedPreservesInv == Inv /\ t_t_step_back_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_step_back_paused, TypeInvariant, States

LEMMA RunPreservesInv == Inv /\ t_t_run => Inv'
BY ConstantsDistinct DEF Inv, t_t_run, TypeInvariant, States

LEMMA RunHibpPreservesInv == Inv /\ t_t_run_hit_bp => Inv'
BY ConstantsDistinct DEF Inv, t_t_run_hit_bp, TypeInvariant, States

LEMMA ContinuePreservesInv == Inv /\ t_t_continue => Inv'
BY ConstantsDistinct DEF Inv, t_t_continue, TypeInvariant, States

LEMMA ContinueRunPreservesInv == Inv /\ t_t_continue_run => Inv'
BY ConstantsDistinct DEF Inv, t_t_continue_run, TypeInvariant, States

LEMMA PausePreservesInv == Inv /\ t_t_pause => Inv'
BY ConstantsDistinct DEF Inv, t_t_pause, TypeInvariant, States

LEMMA StopPreservesInv == Inv /\ t_t_stop => Inv'
BY ConstantsDistinct DEF Inv, t_t_stop, TypeInvariant, States

LEMMA StopPausedPreservesInv == Inv /\ t_t_stop_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_stop_paused, TypeInvariant, States

LEMMA InspecstatePreservesInv == Inv /\ t_t_inspect_state => Inv'
BY ConstantsDistinct DEF Inv, t_t_inspect_state, TypeInvariant, States

LEMMA InspecstatePausedPreservesInv == Inv /\ t_t_inspect_state_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_inspect_state_paused, TypeInvariant, States

LEMMA InspeccontextPreservesInv == Inv /\ t_t_inspect_context => Inv'
BY ConstantsDistinct DEF Inv, t_t_inspect_context, TypeInvariant, States

LEMMA InspeccontexpausedPreservesInv == Inv /\ t_t_inspect_context_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_inspect_context_paused, TypeInvariant, States

LEMMA EvalPreservesInv == Inv /\ t_t_eval => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval, TypeInvariant, States

LEMMA EvalPausedPreservesInv == Inv /\ t_t_eval_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_eval_paused, TypeInvariant, States

LEMMA AddWatchPreservesInv == Inv /\ t_t_add_watch => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_watch, TypeInvariant, States

LEMMA AddWatchPausedPreservesInv == Inv /\ t_t_add_watch_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_add_watch_paused, TypeInvariant, States

LEMMA RemoveWatchPreservesInv == Inv /\ t_t_remove_watch => Inv'
BY ConstantsDistinct DEF Inv, t_t_remove_watch, TypeInvariant, States

LEMMA GewatchesPreservesInv == Inv /\ t_t_get_watches => Inv'
BY ConstantsDistinct DEF Inv, t_t_get_watches, TypeInvariant, States

LEMMA GewatchesPausedPreservesInv == Inv /\ t_t_get_watches_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_get_watches_paused, TypeInvariant, States

LEMMA HistoryPreservesInv == Inv /\ t_t_history => Inv'
BY ConstantsDistinct DEF Inv, t_t_history, TypeInvariant, States

LEMMA HistoryPausedPreservesInv == Inv /\ t_t_history_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_history_paused, TypeInvariant, States

LEMMA GotoStepPreservesInv == Inv /\ t_t_goto_step => Inv'
BY ConstantsDistinct DEF Inv, t_t_goto_step, TypeInvariant, States

LEMMA GotoStepPausedPreservesInv == Inv /\ t_t_goto_step_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_goto_step_paused, TypeInvariant, States

LEMMA ComparePreservesInv == Inv /\ t_t_compare => Inv'
BY ConstantsDistinct DEF Inv, t_t_compare, TypeInvariant, States

LEMMA ComparePausedPreservesInv == Inv /\ t_t_compare_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_compare_paused, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA ResepausedPreservesInv == Inv /\ t_t_reset_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_paused, TypeInvariant, States

LEMMA StatusPreservesInv == Inv /\ t_t_status => Inv'
BY ConstantsDistinct DEF Inv, t_t_status, TypeInvariant, States

LEMMA StatusPausedPreservesInv == Inv /\ t_t_status_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_status_paused, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadDebugPreservesInv == Inv /\ t_t_unload_debug => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_debug, TypeInvariant, States

LEMMA UnloadPausedPreservesInv == Inv /\ t_t_unload_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_paused, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, LoadErrorPreservesInv, ReloadPreservesInv, ReloadFromDebugPreservesInv, StardebugPreservesInv, SebpLoadedPreservesInv, SebpDebugPreservesInv, SebpPausedPreservesInv, RemoveBpDebugPreservesInv, RemoveBpPausedPreservesInv, LisbpDebugPreservesInv, LisbpPausedPreservesInv, StepPreservesInv, StepToPausedPreservesInv, StepOverPreservesInv, StepBackPreservesInv, StepBackPausedPreservesInv, RunPreservesInv, RunHibpPreservesInv, ContinuePreservesInv, ContinueRunPreservesInv, PausePreservesInv, StopPreservesInv, StopPausedPreservesInv, InspecstatePreservesInv, InspecstatePausedPreservesInv, InspeccontextPreservesInv, InspeccontexpausedPreservesInv, EvalPreservesInv, EvalPausedPreservesInv, AddWatchPreservesInv, AddWatchPausedPreservesInv, RemoveWatchPreservesInv, GewatchesPreservesInv, GewatchesPausedPreservesInv, HistoryPreservesInv, HistoryPausedPreservesInv, GotoStepPreservesInv, GotoStepPausedPreservesInv, ComparePreservesInv, ComparePausedPreservesInv, ResetPreservesInv, ResepausedPreservesInv, StatusPreservesInv, StatusPausedPreservesInv, UnloadPreservesInv, UnloadDebugPreservesInv, UnloadPausedPreservesInv, RecoverPreservesInv DEF Next

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