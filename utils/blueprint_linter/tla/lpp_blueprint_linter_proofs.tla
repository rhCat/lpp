--------------------------- MODULE lpp_blueprint_linter_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Linter
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loaded, STATE_linting, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loaded
    /\ STATE_idle /= STATE_linting
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_loaded /= STATE_linting
    /\ STATE_loaded /= STATE_complete
    /\ STATE_loaded /= STATE_error
    /\ STATE_linting /= STATE_complete
    /\ STATE_linting /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loaded, STATE_linting, STATE_complete, STATE_error}
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

(* Transition: t_reload_from_complete *)
t_t_reload_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_loaded

(* Transition: t_start_lint *)
t_t_start_lint ==
    /\ state = STATE_loaded
    /\ state' = STATE_linting

(* Transition: t_check_unreachable *)
t_t_check_unreachable ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_dead_end *)
t_t_check_dead_end ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_unused_gates *)
t_t_check_unused_gates ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_unused_actions *)
t_t_check_unused_actions ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_unused_context *)
t_t_check_unused_context ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_orphaned *)
t_t_check_orphaned ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_gate_refs *)
t_t_check_gate_refs ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_action_refs *)
t_t_check_action_refs ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_duplicates *)
t_t_check_duplicates ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_check_naming *)
t_t_check_naming ==
    /\ state = STATE_linting
    /\ state' = STATE_linting

(* Transition: t_finalize *)
t_t_finalize ==
    /\ state = STATE_linting
    /\ state' = STATE_complete

(* Transition: t_run_all *)
t_t_run_all ==
    /\ state = STATE_loaded
    /\ state' = STATE_complete

(* Transition: t_relint *)
t_t_relint ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_back_to_loaded *)
t_t_back_to_loaded ==
    /\ state = STATE_complete
    /\ state' = STATE_loaded

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_loaded
    /\ state' = STATE_idle

(* Transition: t_unload_from_complete *)
t_t_unload_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

(* Transition: t_configure *)
t_t_configure ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t_configure_loaded *)
t_t_configure_loaded ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_load
    \/ t_t_load_error
    \/ t_t_reload
    \/ t_t_reload_from_complete
    \/ t_t_start_lint
    \/ t_t_check_unreachable
    \/ t_t_check_dead_end
    \/ t_t_check_unused_gates
    \/ t_t_check_unused_actions
    \/ t_t_check_unused_context
    \/ t_t_check_orphaned
    \/ t_t_check_gate_refs
    \/ t_t_check_action_refs
    \/ t_t_check_duplicates
    \/ t_t_check_naming
    \/ t_t_finalize
    \/ t_t_run_all
    \/ t_t_relint
    \/ t_t_back_to_loaded
    \/ t_t_unload
    \/ t_t_unload_from_complete
    \/ t_t_configure
    \/ t_t_configure_loaded
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

LEMMA ReloadFromCompletePreservesInv == Inv /\ t_t_reload_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_complete, TypeInvariant, States

LEMMA StarlintPreservesInv == Inv /\ t_t_start_lint => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_lint, TypeInvariant, States

LEMMA CheckUnreachablePreservesInv == Inv /\ t_t_check_unreachable => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_unreachable, TypeInvariant, States

LEMMA CheckDeadEndPreservesInv == Inv /\ t_t_check_dead_end => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_dead_end, TypeInvariant, States

LEMMA CheckUnusedGatesPreservesInv == Inv /\ t_t_check_unused_gates => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_unused_gates, TypeInvariant, States

LEMMA CheckUnusedActionsPreservesInv == Inv /\ t_t_check_unused_actions => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_unused_actions, TypeInvariant, States

LEMMA CheckUnusedContextPreservesInv == Inv /\ t_t_check_unused_context => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_unused_context, TypeInvariant, States

LEMMA CheckOrphanedPreservesInv == Inv /\ t_t_check_orphaned => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_orphaned, TypeInvariant, States

LEMMA CheckGateRefsPreservesInv == Inv /\ t_t_check_gate_refs => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_gate_refs, TypeInvariant, States

LEMMA CheckActionRefsPreservesInv == Inv /\ t_t_check_action_refs => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_action_refs, TypeInvariant, States

LEMMA CheckDuplicatesPreservesInv == Inv /\ t_t_check_duplicates => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_duplicates, TypeInvariant, States

LEMMA CheckNamingPreservesInv == Inv /\ t_t_check_naming => Inv'
BY ConstantsDistinct DEF Inv, t_t_check_naming, TypeInvariant, States

LEMMA FinalizePreservesInv == Inv /\ t_t_finalize => Inv'
BY ConstantsDistinct DEF Inv, t_t_finalize, TypeInvariant, States

LEMMA RunAllPreservesInv == Inv /\ t_t_run_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_run_all, TypeInvariant, States

LEMMA RelintPreservesInv == Inv /\ t_t_relint => Inv'
BY ConstantsDistinct DEF Inv, t_t_relint, TypeInvariant, States

LEMMA BackToLoadedPreservesInv == Inv /\ t_t_back_to_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_loaded, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadFromCompletePreservesInv == Inv /\ t_t_unload_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_complete, TypeInvariant, States

LEMMA ConfigurePreservesInv == Inv /\ t_t_configure => Inv'
BY ConstantsDistinct DEF Inv, t_t_configure, TypeInvariant, States

LEMMA ConfigureLoadedPreservesInv == Inv /\ t_t_configure_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_configure_loaded, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, LoadErrorPreservesInv, ReloadPreservesInv, ReloadFromCompletePreservesInv, StarlintPreservesInv, CheckUnreachablePreservesInv, CheckDeadEndPreservesInv, CheckUnusedGatesPreservesInv, CheckUnusedActionsPreservesInv, CheckUnusedContextPreservesInv, CheckOrphanedPreservesInv, CheckGateRefsPreservesInv, CheckActionRefsPreservesInv, CheckDuplicatesPreservesInv, CheckNamingPreservesInv, FinalizePreservesInv, RunAllPreservesInv, RelintPreservesInv, BackToLoadedPreservesInv, UnloadPreservesInv, UnloadFromCompletePreservesInv, ConfigurePreservesInv, ConfigureLoadedPreservesInv, RecoverPreservesInv DEF Next

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