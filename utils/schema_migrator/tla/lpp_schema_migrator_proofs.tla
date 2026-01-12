--------------------------- MODULE lpp_schema_migrator_proofs ---------------------------
(*
 * L++ Blueprint: L++ Schema Migrator
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loaded, STATE_planning, STATE_planned, STATE_migrating, STATE_validating, STATE_complete, STATE_batch_mode, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loaded
    /\ STATE_idle /= STATE_planning
    /\ STATE_idle /= STATE_planned
    /\ STATE_idle /= STATE_migrating
    /\ STATE_idle /= STATE_validating
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_batch_mode
    /\ STATE_idle /= STATE_error
    /\ STATE_loaded /= STATE_planning
    /\ STATE_loaded /= STATE_planned
    /\ STATE_loaded /= STATE_migrating
    /\ STATE_loaded /= STATE_validating
    /\ STATE_loaded /= STATE_complete
    /\ STATE_loaded /= STATE_batch_mode
    /\ STATE_loaded /= STATE_error
    /\ STATE_planning /= STATE_planned
    /\ STATE_planning /= STATE_migrating
    /\ STATE_planning /= STATE_validating
    /\ STATE_planning /= STATE_complete
    /\ STATE_planning /= STATE_batch_mode
    /\ STATE_planning /= STATE_error
    /\ STATE_planned /= STATE_migrating
    /\ STATE_planned /= STATE_validating
    /\ STATE_planned /= STATE_complete
    /\ STATE_planned /= STATE_batch_mode
    /\ STATE_planned /= STATE_error
    /\ STATE_migrating /= STATE_validating
    /\ STATE_migrating /= STATE_complete
    /\ STATE_migrating /= STATE_batch_mode
    /\ STATE_migrating /= STATE_error
    /\ STATE_validating /= STATE_complete
    /\ STATE_validating /= STATE_batch_mode
    /\ STATE_validating /= STATE_error
    /\ STATE_complete /= STATE_batch_mode
    /\ STATE_complete /= STATE_error
    /\ STATE_batch_mode /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loaded, STATE_planning, STATE_planned, STATE_migrating, STATE_validating, STATE_complete, STATE_batch_mode, STATE_error}
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

(* Transition: t_set_target *)
t_t_set_target ==
    /\ state = STATE_loaded
    /\ state' = STATE_planning

(* Transition: t_set_target_latest *)
t_t_set_target_latest ==
    /\ state = STATE_loaded
    /\ state' = STATE_planning

(* Transition: t_plan *)
t_t_plan ==
    /\ state = STATE_planning
    /\ state' = STATE_planned

(* Transition: t_auto_plan *)
t_t_auto_plan ==
    /\ state = STATE_loaded
    /\ state' = STATE_planned

(* Transition: t_auto_plan_latest *)
t_t_auto_plan_latest ==
    /\ state = STATE_loaded
    /\ state' = STATE_planned

(* Transition: t_dry_run *)
t_t_dry_run ==
    /\ state = STATE_planned
    /\ state' = STATE_complete

(* Transition: t_execute *)
t_t_execute ==
    /\ state = STATE_planned
    /\ state' = STATE_migrating

(* Transition: t_validate *)
t_t_validate ==
    /\ state = STATE_migrating
    /\ state' = STATE_validating

(* Transition: t_auto_validate *)
t_t_auto_validate ==
    /\ state = STATE_migrating
    /\ state' = STATE_validating

(* Transition: t_finalize *)
t_t_finalize ==
    /\ state = STATE_validating
    /\ state' = STATE_complete

(* Transition: t_finalize_with_warnings *)
t_t_finalize_with_warnings ==
    /\ state = STATE_validating
    /\ state' = STATE_complete

(* Transition: t_migrate_all *)
t_t_migrate_all ==
    /\ state = STATE_loaded
    /\ state' = STATE_complete

(* Transition: t_preview_all *)
t_t_preview_all ==
    /\ state = STATE_loaded
    /\ state' = STATE_complete

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_start_batch *)
t_t_start_batch ==
    /\ state = STATE_idle
    /\ state' = STATE_batch_mode

(* Transition: t_batch_with_target *)
t_t_batch_with_target ==
    /\ state = STATE_idle
    /\ state' = STATE_batch_mode

(* Transition: t_run_batch *)
t_t_run_batch ==
    /\ state = STATE_batch_mode
    /\ state' = STATE_complete

(* Transition: t_back_to_loaded *)
t_t_back_to_loaded ==
    /\ state = STATE_planned
    /\ state' = STATE_loaded

(* Transition: t_back_from_complete *)
t_t_back_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_loaded

(* Transition: t_replan *)
t_t_replan ==
    /\ state = STATE_planned
    /\ state' = STATE_planning

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_loaded
    /\ state' = STATE_idle

(* Transition: t_unload_from_complete *)
t_t_unload_from_complete ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

(* Transition: t_unload_from_planned *)
t_t_unload_from_planned ==
    /\ state = STATE_planned
    /\ state' = STATE_idle

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_recover_to_loaded *)
t_t_recover_to_loaded ==
    /\ state = STATE_error
    /\ state' = STATE_loaded

Next ==
    \/ t_t_load
    \/ t_t_load_error
    \/ t_t_reload
    \/ t_t_reload_from_complete
    \/ t_t_set_target
    \/ t_t_set_target_latest
    \/ t_t_plan
    \/ t_t_auto_plan
    \/ t_t_auto_plan_latest
    \/ t_t_dry_run
    \/ t_t_execute
    \/ t_t_validate
    \/ t_t_auto_validate
    \/ t_t_finalize
    \/ t_t_finalize_with_warnings
    \/ t_t_migrate_all
    \/ t_t_preview_all
    \/ t_t_export
    \/ t_t_start_batch
    \/ t_t_batch_with_target
    \/ t_t_run_batch
    \/ t_t_back_to_loaded
    \/ t_t_back_from_complete
    \/ t_t_replan
    \/ t_t_unload
    \/ t_t_unload_from_complete
    \/ t_t_unload_from_planned
    \/ t_t_recover
    \/ t_t_recover_to_loaded

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

LEMMA SetargetPreservesInv == Inv /\ t_t_set_target => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_target, TypeInvariant, States

LEMMA SetargelatestPreservesInv == Inv /\ t_t_set_target_latest => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_target_latest, TypeInvariant, States

LEMMA PlanPreservesInv == Inv /\ t_t_plan => Inv'
BY ConstantsDistinct DEF Inv, t_t_plan, TypeInvariant, States

LEMMA AutoPlanPreservesInv == Inv /\ t_t_auto_plan => Inv'
BY ConstantsDistinct DEF Inv, t_t_auto_plan, TypeInvariant, States

LEMMA AutoPlanLatestPreservesInv == Inv /\ t_t_auto_plan_latest => Inv'
BY ConstantsDistinct DEF Inv, t_t_auto_plan_latest, TypeInvariant, States

LEMMA DryRunPreservesInv == Inv /\ t_t_dry_run => Inv'
BY ConstantsDistinct DEF Inv, t_t_dry_run, TypeInvariant, States

LEMMA ExecutePreservesInv == Inv /\ t_t_execute => Inv'
BY ConstantsDistinct DEF Inv, t_t_execute, TypeInvariant, States

LEMMA ValidatePreservesInv == Inv /\ t_t_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_validate, TypeInvariant, States

LEMMA AutoValidatePreservesInv == Inv /\ t_t_auto_validate => Inv'
BY ConstantsDistinct DEF Inv, t_t_auto_validate, TypeInvariant, States

LEMMA FinalizePreservesInv == Inv /\ t_t_finalize => Inv'
BY ConstantsDistinct DEF Inv, t_t_finalize, TypeInvariant, States

LEMMA FinalizeWithWarningsPreservesInv == Inv /\ t_t_finalize_with_warnings => Inv'
BY ConstantsDistinct DEF Inv, t_t_finalize_with_warnings, TypeInvariant, States

LEMMA MigrateAllPreservesInv == Inv /\ t_t_migrate_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_migrate_all, TypeInvariant, States

LEMMA PreviewAllPreservesInv == Inv /\ t_t_preview_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_preview_all, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA StarbatchPreservesInv == Inv /\ t_t_start_batch => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_batch, TypeInvariant, States

LEMMA BatchWithTargetPreservesInv == Inv /\ t_t_batch_with_target => Inv'
BY ConstantsDistinct DEF Inv, t_t_batch_with_target, TypeInvariant, States

LEMMA RunBatchPreservesInv == Inv /\ t_t_run_batch => Inv'
BY ConstantsDistinct DEF Inv, t_t_run_batch, TypeInvariant, States

LEMMA BackToLoadedPreservesInv == Inv /\ t_t_back_to_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_loaded, TypeInvariant, States

LEMMA BackFromCompletePreservesInv == Inv /\ t_t_back_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_complete, TypeInvariant, States

LEMMA ReplanPreservesInv == Inv /\ t_t_replan => Inv'
BY ConstantsDistinct DEF Inv, t_t_replan, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadFromCompletePreservesInv == Inv /\ t_t_unload_from_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_complete, TypeInvariant, States

LEMMA UnloadFromPlannedPreservesInv == Inv /\ t_t_unload_from_planned => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_planned, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA RecoverToLoadedPreservesInv == Inv /\ t_t_recover_to_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover_to_loaded, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, LoadErrorPreservesInv, ReloadPreservesInv, ReloadFromCompletePreservesInv, SetargetPreservesInv, SetargelatestPreservesInv, PlanPreservesInv, AutoPlanPreservesInv, AutoPlanLatestPreservesInv, DryRunPreservesInv, ExecutePreservesInv, ValidatePreservesInv, AutoValidatePreservesInv, FinalizePreservesInv, FinalizeWithWarningsPreservesInv, MigrateAllPreservesInv, PreviewAllPreservesInv, ExportPreservesInv, StarbatchPreservesInv, BatchWithTargetPreservesInv, RunBatchPreservesInv, BackToLoadedPreservesInv, BackFromCompletePreservesInv, ReplanPreservesInv, UnloadPreservesInv, UnloadFromCompletePreservesInv, UnloadFromPlannedPreservesInv, RecoverPreservesInv, RecoverToLoadedPreservesInv DEF Next

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