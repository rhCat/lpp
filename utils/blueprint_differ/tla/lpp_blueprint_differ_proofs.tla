--------------------------- MODULE lpp_blueprint_differ_proofs ---------------------------
(*
 * L++ Blueprint: L++ Blueprint Diff & Merge
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_left_loaded, STATE_ready, STATE_diffing, STATE_diff_complete, STATE_merging, STATE_merge_complete, STATE_conflict, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_left_loaded
    /\ STATE_idle /= STATE_ready
    /\ STATE_idle /= STATE_diffing
    /\ STATE_idle /= STATE_diff_complete
    /\ STATE_idle /= STATE_merging
    /\ STATE_idle /= STATE_merge_complete
    /\ STATE_idle /= STATE_conflict
    /\ STATE_idle /= STATE_error
    /\ STATE_left_loaded /= STATE_ready
    /\ STATE_left_loaded /= STATE_diffing
    /\ STATE_left_loaded /= STATE_diff_complete
    /\ STATE_left_loaded /= STATE_merging
    /\ STATE_left_loaded /= STATE_merge_complete
    /\ STATE_left_loaded /= STATE_conflict
    /\ STATE_left_loaded /= STATE_error
    /\ STATE_ready /= STATE_diffing
    /\ STATE_ready /= STATE_diff_complete
    /\ STATE_ready /= STATE_merging
    /\ STATE_ready /= STATE_merge_complete
    /\ STATE_ready /= STATE_conflict
    /\ STATE_ready /= STATE_error
    /\ STATE_diffing /= STATE_diff_complete
    /\ STATE_diffing /= STATE_merging
    /\ STATE_diffing /= STATE_merge_complete
    /\ STATE_diffing /= STATE_conflict
    /\ STATE_diffing /= STATE_error
    /\ STATE_diff_complete /= STATE_merging
    /\ STATE_diff_complete /= STATE_merge_complete
    /\ STATE_diff_complete /= STATE_conflict
    /\ STATE_diff_complete /= STATE_error
    /\ STATE_merging /= STATE_merge_complete
    /\ STATE_merging /= STATE_conflict
    /\ STATE_merging /= STATE_error
    /\ STATE_merge_complete /= STATE_conflict
    /\ STATE_merge_complete /= STATE_error
    /\ STATE_conflict /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_left_loaded, STATE_ready, STATE_diffing, STATE_diff_complete, STATE_merging, STATE_merge_complete, STATE_conflict, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load_left_from_idle *)
t_t_load_left_from_idle ==
    /\ state = STATE_idle
    /\ state' = STATE_left_loaded

(* Transition: t_load_right_from_left *)
t_t_load_right_from_left ==
    /\ state = STATE_left_loaded
    /\ state' = STATE_ready

(* Transition: t_load_base_from_ready *)
t_t_load_base_from_ready ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_reload_left *)
t_t_reload_left ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_reload_right *)
t_t_reload_right ==
    /\ state = STATE_ready
    /\ state' = STATE_ready

(* Transition: t_start_diff *)
t_t_start_diff ==
    /\ state = STATE_ready
    /\ state' = STATE_diffing

(* Transition: t_diff_to_complete *)
t_t_diff_to_complete ==
    /\ state = STATE_diffing
    /\ state' = STATE_diff_complete

(* Transition: t_auto_diff_complete *)
t_t_auto_diff_complete ==
    /\ state = STATE_ready
    /\ state' = STATE_diff_complete

(* Transition: t_show_summary *)
t_t_show_summary ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_diff_complete

(* Transition: t_show_unified *)
t_t_show_unified ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_diff_complete

(* Transition: t_show_patch *)
t_t_show_patch ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_diff_complete

(* Transition: t_start_merge *)
t_t_start_merge ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_merging

(* Transition: t_merge_no_conflict *)
t_t_merge_no_conflict ==
    /\ state = STATE_merging
    /\ state' = STATE_merge_complete

(* Transition: t_merge_conflict_detected *)
t_t_merge_conflict_detected ==
    /\ state = STATE_merging
    /\ state' = STATE_conflict

(* Transition: t_resolve_take_left *)
t_t_resolve_take_left ==
    /\ state = STATE_conflict
    /\ state' = STATE_merge_complete

(* Transition: t_resolve_take_right *)
t_t_resolve_take_right ==
    /\ state = STATE_conflict
    /\ state' = STATE_merge_complete

(* Transition: t_force_merge_left *)
t_t_force_merge_left ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_merge_complete

(* Transition: t_force_merge_right *)
t_t_force_merge_right ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_merge_complete

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_merge_complete
    /\ state' = STATE_merge_complete

(* Transition: t_back_to_diff *)
t_t_back_to_diff ==
    /\ state = STATE_merge_complete
    /\ state' = STATE_diff_complete

(* Transition: t_back_from_conflict *)
t_t_back_from_conflict ==
    /\ state = STATE_conflict
    /\ state' = STATE_diff_complete

(* Transition: t_rediff *)
t_t_rediff ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_diff_complete

(* Transition: t_back_to_ready *)
t_t_back_to_ready ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_ready

(* Transition: t_clear_all *)
t_t_clear_all ==
    /\ state = STATE_ready
    /\ state' = STATE_idle

(* Transition: t_clear_from_diff *)
t_t_clear_from_diff ==
    /\ state = STATE_diff_complete
    /\ state' = STATE_idle

(* Transition: t_clear_from_merge *)
t_t_clear_from_merge ==
    /\ state = STATE_merge_complete
    /\ state' = STATE_idle

(* Transition: t_error_recover *)
t_t_error_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

(* Transition: t_load_error *)
t_t_load_error ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

Next ==
    \/ t_t_load_left_from_idle
    \/ t_t_load_right_from_left
    \/ t_t_load_base_from_ready
    \/ t_t_reload_left
    \/ t_t_reload_right
    \/ t_t_start_diff
    \/ t_t_diff_to_complete
    \/ t_t_auto_diff_complete
    \/ t_t_show_summary
    \/ t_t_show_unified
    \/ t_t_show_patch
    \/ t_t_start_merge
    \/ t_t_merge_no_conflict
    \/ t_t_merge_conflict_detected
    \/ t_t_resolve_take_left
    \/ t_t_resolve_take_right
    \/ t_t_force_merge_left
    \/ t_t_force_merge_right
    \/ t_t_export
    \/ t_t_back_to_diff
    \/ t_t_back_from_conflict
    \/ t_t_rediff
    \/ t_t_back_to_ready
    \/ t_t_clear_all
    \/ t_t_clear_from_diff
    \/ t_t_clear_from_merge
    \/ t_t_error_recover
    \/ t_t_load_error

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadLeffromIdlePreservesInv == Inv /\ t_t_load_left_from_idle => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_left_from_idle, TypeInvariant, States

LEMMA LoadRighfromLeftPreservesInv == Inv /\ t_t_load_right_from_left => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_right_from_left, TypeInvariant, States

LEMMA LoadBaseFromReadyPreservesInv == Inv /\ t_t_load_base_from_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_base_from_ready, TypeInvariant, States

LEMMA ReloadLeftPreservesInv == Inv /\ t_t_reload_left => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_left, TypeInvariant, States

LEMMA ReloadRightPreservesInv == Inv /\ t_t_reload_right => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_right, TypeInvariant, States

LEMMA StardiffPreservesInv == Inv /\ t_t_start_diff => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_diff, TypeInvariant, States

LEMMA DiffToCompletePreservesInv == Inv /\ t_t_diff_to_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_diff_to_complete, TypeInvariant, States

LEMMA AutoDiffCompletePreservesInv == Inv /\ t_t_auto_diff_complete => Inv'
BY ConstantsDistinct DEF Inv, t_t_auto_diff_complete, TypeInvariant, States

LEMMA ShowSummaryPreservesInv == Inv /\ t_t_show_summary => Inv'
BY ConstantsDistinct DEF Inv, t_t_show_summary, TypeInvariant, States

LEMMA ShowUnifiedPreservesInv == Inv /\ t_t_show_unified => Inv'
BY ConstantsDistinct DEF Inv, t_t_show_unified, TypeInvariant, States

LEMMA ShowPatchPreservesInv == Inv /\ t_t_show_patch => Inv'
BY ConstantsDistinct DEF Inv, t_t_show_patch, TypeInvariant, States

LEMMA StarmergePreservesInv == Inv /\ t_t_start_merge => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_merge, TypeInvariant, States

LEMMA MergeNoConflictPreservesInv == Inv /\ t_t_merge_no_conflict => Inv'
BY ConstantsDistinct DEF Inv, t_t_merge_no_conflict, TypeInvariant, States

LEMMA MergeConflicdetectedPreservesInv == Inv /\ t_t_merge_conflict_detected => Inv'
BY ConstantsDistinct DEF Inv, t_t_merge_conflict_detected, TypeInvariant, States

LEMMA ResolveTakeLeftPreservesInv == Inv /\ t_t_resolve_take_left => Inv'
BY ConstantsDistinct DEF Inv, t_t_resolve_take_left, TypeInvariant, States

LEMMA ResolveTakeRightPreservesInv == Inv /\ t_t_resolve_take_right => Inv'
BY ConstantsDistinct DEF Inv, t_t_resolve_take_right, TypeInvariant, States

LEMMA ForceMergeLeftPreservesInv == Inv /\ t_t_force_merge_left => Inv'
BY ConstantsDistinct DEF Inv, t_t_force_merge_left, TypeInvariant, States

LEMMA ForceMergeRightPreservesInv == Inv /\ t_t_force_merge_right => Inv'
BY ConstantsDistinct DEF Inv, t_t_force_merge_right, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA BackToDiffPreservesInv == Inv /\ t_t_back_to_diff => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_diff, TypeInvariant, States

LEMMA BackFromConflictPreservesInv == Inv /\ t_t_back_from_conflict => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_from_conflict, TypeInvariant, States

LEMMA RediffPreservesInv == Inv /\ t_t_rediff => Inv'
BY ConstantsDistinct DEF Inv, t_t_rediff, TypeInvariant, States

LEMMA BackToReadyPreservesInv == Inv /\ t_t_back_to_ready => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_ready, TypeInvariant, States

LEMMA ClearAllPreservesInv == Inv /\ t_t_clear_all => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear_all, TypeInvariant, States

LEMMA ClearFromDiffPreservesInv == Inv /\ t_t_clear_from_diff => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear_from_diff, TypeInvariant, States

LEMMA ClearFromMergePreservesInv == Inv /\ t_t_clear_from_merge => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear_from_merge, TypeInvariant, States

LEMMA ErrorRecoverPreservesInv == Inv /\ t_t_error_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_recover, TypeInvariant, States

LEMMA LoadErrorPreservesInv == Inv /\ t_t_load_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_error, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadLeffromIdlePreservesInv, LoadRighfromLeftPreservesInv, LoadBaseFromReadyPreservesInv, ReloadLeftPreservesInv, ReloadRightPreservesInv, StardiffPreservesInv, DiffToCompletePreservesInv, AutoDiffCompletePreservesInv, ShowSummaryPreservesInv, ShowUnifiedPreservesInv, ShowPatchPreservesInv, StarmergePreservesInv, MergeNoConflictPreservesInv, MergeConflicdetectedPreservesInv, ResolveTakeLeftPreservesInv, ResolveTakeRightPreservesInv, ForceMergeLeftPreservesInv, ForceMergeRightPreservesInv, ExportPreservesInv, BackToDiffPreservesInv, BackFromConflictPreservesInv, RediffPreservesInv, BackToReadyPreservesInv, ClearAllPreservesInv, ClearFromDiffPreservesInv, ClearFromMergePreservesInv, ErrorRecoverPreservesInv, LoadErrorPreservesInv DEF Next

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