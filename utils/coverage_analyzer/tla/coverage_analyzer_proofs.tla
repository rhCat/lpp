--------------------------- MODULE coverage_analyzer_proofs ---------------------------
(*
 * L++ Blueprint: L++ Coverage Analyzer
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loaded, STATE_tracking, STATE_analyzing, STATE_reporting, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loaded
    /\ STATE_idle /= STATE_tracking
    /\ STATE_idle /= STATE_analyzing
    /\ STATE_idle /= STATE_reporting
    /\ STATE_idle /= STATE_error
    /\ STATE_loaded /= STATE_tracking
    /\ STATE_loaded /= STATE_analyzing
    /\ STATE_loaded /= STATE_reporting
    /\ STATE_loaded /= STATE_error
    /\ STATE_tracking /= STATE_analyzing
    /\ STATE_tracking /= STATE_reporting
    /\ STATE_tracking /= STATE_error
    /\ STATE_analyzing /= STATE_reporting
    /\ STATE_analyzing /= STATE_error
    /\ STATE_reporting /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loaded, STATE_tracking, STATE_analyzing, STATE_reporting, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_load *)
t_t_load ==
    /\ state = STATE_idle
    /\ state' = STATE_loaded

(* Transition: t_reload *)
t_t_reload ==
    /\ state = STATE_loaded
    /\ state' = STATE_loaded

(* Transition: t_reload_from_tracking *)
t_t_reload_from_tracking ==
    /\ state = STATE_tracking
    /\ state' = STATE_loaded

(* Transition: t_reload_from_analyzing *)
t_t_reload_from_analyzing ==
    /\ state = STATE_analyzing
    /\ state' = STATE_loaded

(* Transition: t_reload_from_reporting *)
t_t_reload_from_reporting ==
    /\ state = STATE_reporting
    /\ state' = STATE_loaded

(* Transition: t_start_tracking *)
t_t_start_tracking ==
    /\ state = STATE_loaded
    /\ state' = STATE_tracking

(* Transition: t_record_state *)
t_t_record_state ==
    /\ state = STATE_tracking
    /\ state' = STATE_tracking

(* Transition: t_record_transition *)
t_t_record_transition ==
    /\ state = STATE_tracking
    /\ state' = STATE_tracking

(* Transition: t_record_gate *)
t_t_record_gate ==
    /\ state = STATE_tracking
    /\ state' = STATE_tracking

(* Transition: t_record_action *)
t_t_record_action ==
    /\ state = STATE_tracking
    /\ state' = STATE_tracking

(* Transition: t_record_event *)
t_t_record_event ==
    /\ state = STATE_tracking
    /\ state' = STATE_tracking

(* Transition: t_import_trace_loaded *)
t_t_import_trace_loaded ==
    /\ state = STATE_loaded
    /\ state' = STATE_tracking

(* Transition: t_import_trace_tracking *)
t_t_import_trace_tracking ==
    /\ state = STATE_tracking
    /\ state' = STATE_tracking

(* Transition: t_analyze *)
t_t_analyze ==
    /\ state = STATE_tracking
    /\ state' = STATE_analyzing

(* Transition: t_analyze_from_loaded *)
t_t_analyze_from_loaded ==
    /\ state = STATE_loaded
    /\ state' = STATE_analyzing

(* Transition: t_summary *)
t_t_summary ==
    /\ state = STATE_analyzing
    /\ state' = STATE_reporting

(* Transition: t_detailed *)
t_t_detailed ==
    /\ state = STATE_analyzing
    /\ state' = STATE_reporting

(* Transition: t_gap *)
t_t_gap ==
    /\ state = STATE_analyzing
    /\ state' = STATE_reporting

(* Transition: t_all_reports *)
t_t_all_reports ==
    /\ state = STATE_analyzing
    /\ state' = STATE_reporting

(* Transition: t_export_html *)
t_t_export_html ==
    /\ state = STATE_reporting
    /\ state' = STATE_reporting

(* Transition: t_export_html_from_analyzing *)
t_t_export_html_from_analyzing ==
    /\ state = STATE_analyzing
    /\ state' = STATE_reporting

(* Transition: t_export_json *)
t_t_export_json ==
    /\ state = STATE_reporting
    /\ state' = STATE_reporting

(* Transition: t_export_json_from_analyzing *)
t_t_export_json_from_analyzing ==
    /\ state = STATE_analyzing
    /\ state' = STATE_reporting

(* Transition: t_more_summary *)
t_t_more_summary ==
    /\ state = STATE_reporting
    /\ state' = STATE_reporting

(* Transition: t_more_detailed *)
t_t_more_detailed ==
    /\ state = STATE_reporting
    /\ state' = STATE_reporting

(* Transition: t_more_gap *)
t_t_more_gap ==
    /\ state = STATE_reporting
    /\ state' = STATE_reporting

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_tracking
    /\ state' = STATE_loaded

(* Transition: t_reset_from_analyzing *)
t_t_reset_from_analyzing ==
    /\ state = STATE_analyzing
    /\ state' = STATE_loaded

(* Transition: t_reset_from_reporting *)
t_t_reset_from_reporting ==
    /\ state = STATE_reporting
    /\ state' = STATE_loaded

(* Transition: t_back_to_tracking *)
t_t_back_to_tracking ==
    /\ state = STATE_analyzing
    /\ state' = STATE_tracking

(* Transition: t_back_to_analyzing *)
t_t_back_to_analyzing ==
    /\ state = STATE_reporting
    /\ state' = STATE_analyzing

(* Transition: t_unload *)
t_t_unload ==
    /\ state = STATE_loaded
    /\ state' = STATE_idle

(* Transition: t_unload_from_tracking *)
t_t_unload_from_tracking ==
    /\ state = STATE_tracking
    /\ state' = STATE_idle

(* Transition: t_unload_from_analyzing *)
t_t_unload_from_analyzing ==
    /\ state = STATE_analyzing
    /\ state' = STATE_idle

(* Transition: t_unload_from_reporting *)
t_t_unload_from_reporting ==
    /\ state = STATE_reporting
    /\ state' = STATE_idle

(* Transition: t_error *)
t_t_error ==
    /\ TRUE  \* Global transition
    /\ state' = STATE_error

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_load
    \/ t_t_reload
    \/ t_t_reload_from_tracking
    \/ t_t_reload_from_analyzing
    \/ t_t_reload_from_reporting
    \/ t_t_start_tracking
    \/ t_t_record_state
    \/ t_t_record_transition
    \/ t_t_record_gate
    \/ t_t_record_action
    \/ t_t_record_event
    \/ t_t_import_trace_loaded
    \/ t_t_import_trace_tracking
    \/ t_t_analyze
    \/ t_t_analyze_from_loaded
    \/ t_t_summary
    \/ t_t_detailed
    \/ t_t_gap
    \/ t_t_all_reports
    \/ t_t_export_html
    \/ t_t_export_html_from_analyzing
    \/ t_t_export_json
    \/ t_t_export_json_from_analyzing
    \/ t_t_more_summary
    \/ t_t_more_detailed
    \/ t_t_more_gap
    \/ t_t_reset
    \/ t_t_reset_from_analyzing
    \/ t_t_reset_from_reporting
    \/ t_t_back_to_tracking
    \/ t_t_back_to_analyzing
    \/ t_t_unload
    \/ t_t_unload_from_tracking
    \/ t_t_unload_from_analyzing
    \/ t_t_unload_from_reporting
    \/ t_t_error
    \/ t_t_recover

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA LoadPreservesInv == Inv /\ t_t_load => Inv'
BY ConstantsDistinct DEF Inv, t_t_load, TypeInvariant, States

LEMMA ReloadPreservesInv == Inv /\ t_t_reload => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload, TypeInvariant, States

LEMMA ReloadFromTrackingPreservesInv == Inv /\ t_t_reload_from_tracking => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_tracking, TypeInvariant, States

LEMMA ReloadFromAnalyzingPreservesInv == Inv /\ t_t_reload_from_analyzing => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_analyzing, TypeInvariant, States

LEMMA ReloadFromReportingPreservesInv == Inv /\ t_t_reload_from_reporting => Inv'
BY ConstantsDistinct DEF Inv, t_t_reload_from_reporting, TypeInvariant, States

LEMMA StartrackingPreservesInv == Inv /\ t_t_start_tracking => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_tracking, TypeInvariant, States

LEMMA RecordStatePreservesInv == Inv /\ t_t_record_state => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_state, TypeInvariant, States

LEMMA RecordTransitionPreservesInv == Inv /\ t_t_record_transition => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_transition, TypeInvariant, States

LEMMA RecordGatePreservesInv == Inv /\ t_t_record_gate => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_gate, TypeInvariant, States

LEMMA RecordActionPreservesInv == Inv /\ t_t_record_action => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_action, TypeInvariant, States

LEMMA RecordEventPreservesInv == Inv /\ t_t_record_event => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_event, TypeInvariant, States

LEMMA ImportraceLoadedPreservesInv == Inv /\ t_t_import_trace_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_import_trace_loaded, TypeInvariant, States

LEMMA ImportraceTrackingPreservesInv == Inv /\ t_t_import_trace_tracking => Inv'
BY ConstantsDistinct DEF Inv, t_t_import_trace_tracking, TypeInvariant, States

LEMMA AnalyzePreservesInv == Inv /\ t_t_analyze => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze, TypeInvariant, States

LEMMA AnalyzeFromLoadedPreservesInv == Inv /\ t_t_analyze_from_loaded => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze_from_loaded, TypeInvariant, States

LEMMA SummaryPreservesInv == Inv /\ t_t_summary => Inv'
BY ConstantsDistinct DEF Inv, t_t_summary, TypeInvariant, States

LEMMA DetailedPreservesInv == Inv /\ t_t_detailed => Inv'
BY ConstantsDistinct DEF Inv, t_t_detailed, TypeInvariant, States

LEMMA GapPreservesInv == Inv /\ t_t_gap => Inv'
BY ConstantsDistinct DEF Inv, t_t_gap, TypeInvariant, States

LEMMA AllReportsPreservesInv == Inv /\ t_t_all_reports => Inv'
BY ConstantsDistinct DEF Inv, t_t_all_reports, TypeInvariant, States

LEMMA ExporhtmlPreservesInv == Inv /\ t_t_export_html => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_html, TypeInvariant, States

LEMMA ExporhtmlFromAnalyzingPreservesInv == Inv /\ t_t_export_html_from_analyzing => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_html_from_analyzing, TypeInvariant, States

LEMMA ExporjsonPreservesInv == Inv /\ t_t_export_json => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_json, TypeInvariant, States

LEMMA ExporjsonFromAnalyzingPreservesInv == Inv /\ t_t_export_json_from_analyzing => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_json_from_analyzing, TypeInvariant, States

LEMMA MoreSummaryPreservesInv == Inv /\ t_t_more_summary => Inv'
BY ConstantsDistinct DEF Inv, t_t_more_summary, TypeInvariant, States

LEMMA MoreDetailedPreservesInv == Inv /\ t_t_more_detailed => Inv'
BY ConstantsDistinct DEF Inv, t_t_more_detailed, TypeInvariant, States

LEMMA MoreGapPreservesInv == Inv /\ t_t_more_gap => Inv'
BY ConstantsDistinct DEF Inv, t_t_more_gap, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA ResefromAnalyzingPreservesInv == Inv /\ t_t_reset_from_analyzing => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_from_analyzing, TypeInvariant, States

LEMMA ResefromReportingPreservesInv == Inv /\ t_t_reset_from_reporting => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_from_reporting, TypeInvariant, States

LEMMA BackToTrackingPreservesInv == Inv /\ t_t_back_to_tracking => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_tracking, TypeInvariant, States

LEMMA BackToAnalyzingPreservesInv == Inv /\ t_t_back_to_analyzing => Inv'
BY ConstantsDistinct DEF Inv, t_t_back_to_analyzing, TypeInvariant, States

LEMMA UnloadPreservesInv == Inv /\ t_t_unload => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload, TypeInvariant, States

LEMMA UnloadFromTrackingPreservesInv == Inv /\ t_t_unload_from_tracking => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_tracking, TypeInvariant, States

LEMMA UnloadFromAnalyzingPreservesInv == Inv /\ t_t_unload_from_analyzing => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_analyzing, TypeInvariant, States

LEMMA UnloadFromReportingPreservesInv == Inv /\ t_t_unload_from_reporting => Inv'
BY ConstantsDistinct DEF Inv, t_t_unload_from_reporting, TypeInvariant, States

LEMMA ErrorPreservesInv == Inv /\ t_t_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_error, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY LoadPreservesInv, ReloadPreservesInv, ReloadFromTrackingPreservesInv, ReloadFromAnalyzingPreservesInv, ReloadFromReportingPreservesInv, StartrackingPreservesInv, RecordStatePreservesInv, RecordTransitionPreservesInv, RecordGatePreservesInv, RecordActionPreservesInv, RecordEventPreservesInv, ImportraceLoadedPreservesInv, ImportraceTrackingPreservesInv, AnalyzePreservesInv, AnalyzeFromLoadedPreservesInv, SummaryPreservesInv, DetailedPreservesInv, GapPreservesInv, AllReportsPreservesInv, ExporhtmlPreservesInv, ExporhtmlFromAnalyzingPreservesInv, ExporjsonPreservesInv, ExporjsonFromAnalyzingPreservesInv, MoreSummaryPreservesInv, MoreDetailedPreservesInv, MoreGapPreservesInv, ResetPreservesInv, ResefromAnalyzingPreservesInv, ResefromReportingPreservesInv, BackToTrackingPreservesInv, BackToAnalyzingPreservesInv, UnloadPreservesInv, UnloadFromTrackingPreservesInv, UnloadFromAnalyzingPreservesInv, UnloadFromReportingPreservesInv, ErrorPreservesInv, RecoverPreservesInv DEF Next

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