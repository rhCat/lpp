--------------------------- MODULE lpp_execution_tracer_proofs ---------------------------
(*
 * L++ Blueprint: L++ Execution Tracer
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_configured, STATE_tracing, STATE_paused, STATE_completed, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_configured
    /\ STATE_idle /= STATE_tracing
    /\ STATE_idle /= STATE_paused
    /\ STATE_idle /= STATE_completed
    /\ STATE_idle /= STATE_error
    /\ STATE_configured /= STATE_tracing
    /\ STATE_configured /= STATE_paused
    /\ STATE_configured /= STATE_completed
    /\ STATE_configured /= STATE_error
    /\ STATE_tracing /= STATE_paused
    /\ STATE_tracing /= STATE_completed
    /\ STATE_tracing /= STATE_error
    /\ STATE_paused /= STATE_completed
    /\ STATE_paused /= STATE_error
    /\ STATE_completed /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_configured, STATE_tracing, STATE_paused, STATE_completed, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_init *)
t_t_init ==
    /\ state = STATE_idle
    /\ state' = STATE_configured

(* Transition: t_init_error *)
t_t_init_error ==
    /\ state = STATE_idle
    /\ state' = STATE_error

(* Transition: t_reconfigure *)
t_t_reconfigure ==
    /\ state = STATE_configured
    /\ state' = STATE_configured

(* Transition: t_start_trace *)
t_t_start_trace ==
    /\ state = STATE_configured
    /\ state' = STATE_tracing

(* Transition: t_start_trace_idle *)
t_t_start_trace_idle ==
    /\ state = STATE_idle
    /\ state' = STATE_tracing

(* Transition: t_record_span *)
t_t_record_span ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_start_span *)
t_t_start_span ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_end_span *)
t_t_end_span ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_record_state *)
t_t_record_state ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_record_gate *)
t_t_record_gate ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_record_action *)
t_t_record_action ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_record_event *)
t_t_record_event ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_record_context *)
t_t_record_context ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_pause_trace *)
t_t_pause_trace ==
    /\ state = STATE_tracing
    /\ state' = STATE_paused

(* Transition: t_resume_trace *)
t_t_resume_trace ==
    /\ state = STATE_paused
    /\ state' = STATE_tracing

(* Transition: t_end_trace *)
t_t_end_trace ==
    /\ state = STATE_tracing
    /\ state' = STATE_completed

(* Transition: t_end_trace_paused *)
t_t_end_trace_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_completed

(* Transition: t_format_otlp *)
t_t_format_otlp ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_format_jsonl *)
t_t_format_jsonl ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_format_human *)
t_t_format_human ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_format_timeline *)
t_t_format_timeline ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_export *)
t_t_export ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_analyze *)
t_t_analyze ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_status_tracing *)
t_t_status_tracing ==
    /\ state = STATE_tracing
    /\ state' = STATE_tracing

(* Transition: t_status_paused *)
t_t_status_paused ==
    /\ state = STATE_paused
    /\ state' = STATE_paused

(* Transition: t_status_completed *)
t_t_status_completed ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_set_format_conf *)
t_t_set_format_conf ==
    /\ state = STATE_configured
    /\ state' = STATE_configured

(* Transition: t_set_format_completed *)
t_t_set_format_completed ==
    /\ state = STATE_completed
    /\ state' = STATE_completed

(* Transition: t_clear_completed *)
t_t_clear_completed ==
    /\ state = STATE_completed
    /\ state' = STATE_configured

(* Transition: t_new_trace *)
t_t_new_trace ==
    /\ state = STATE_completed
    /\ state' = STATE_tracing

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_configured
    /\ state' = STATE_idle

(* Transition: t_reset_tracing *)
t_t_reset_tracing ==
    /\ state = STATE_tracing
    /\ state' = STATE_idle

(* Transition: t_reset_completed *)
t_t_reset_completed ==
    /\ state = STATE_completed
    /\ state' = STATE_idle

(* Transition: t_recover *)
t_t_recover ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_init
    \/ t_t_init_error
    \/ t_t_reconfigure
    \/ t_t_start_trace
    \/ t_t_start_trace_idle
    \/ t_t_record_span
    \/ t_t_start_span
    \/ t_t_end_span
    \/ t_t_record_state
    \/ t_t_record_gate
    \/ t_t_record_action
    \/ t_t_record_event
    \/ t_t_record_context
    \/ t_t_pause_trace
    \/ t_t_resume_trace
    \/ t_t_end_trace
    \/ t_t_end_trace_paused
    \/ t_t_format_otlp
    \/ t_t_format_jsonl
    \/ t_t_format_human
    \/ t_t_format_timeline
    \/ t_t_export
    \/ t_t_analyze
    \/ t_t_status_tracing
    \/ t_t_status_paused
    \/ t_t_status_completed
    \/ t_t_set_format_conf
    \/ t_t_set_format_completed
    \/ t_t_clear_completed
    \/ t_t_new_trace
    \/ t_t_reset
    \/ t_t_reset_tracing
    \/ t_t_reset_completed
    \/ t_t_recover

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA InitPreservesInv == Inv /\ t_t_init => Inv'
BY ConstantsDistinct DEF Inv, t_t_init, TypeInvariant, States

LEMMA InierrorPreservesInv == Inv /\ t_t_init_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_init_error, TypeInvariant, States

LEMMA ReconfigurePreservesInv == Inv /\ t_t_reconfigure => Inv'
BY ConstantsDistinct DEF Inv, t_t_reconfigure, TypeInvariant, States

LEMMA StartracePreservesInv == Inv /\ t_t_start_trace => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_trace, TypeInvariant, States

LEMMA StartraceIdlePreservesInv == Inv /\ t_t_start_trace_idle => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_trace_idle, TypeInvariant, States

LEMMA RecordSpanPreservesInv == Inv /\ t_t_record_span => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_span, TypeInvariant, States

LEMMA StarspanPreservesInv == Inv /\ t_t_start_span => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_span, TypeInvariant, States

LEMMA EndSpanPreservesInv == Inv /\ t_t_end_span => Inv'
BY ConstantsDistinct DEF Inv, t_t_end_span, TypeInvariant, States

LEMMA RecordStatePreservesInv == Inv /\ t_t_record_state => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_state, TypeInvariant, States

LEMMA RecordGatePreservesInv == Inv /\ t_t_record_gate => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_gate, TypeInvariant, States

LEMMA RecordActionPreservesInv == Inv /\ t_t_record_action => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_action, TypeInvariant, States

LEMMA RecordEventPreservesInv == Inv /\ t_t_record_event => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_event, TypeInvariant, States

LEMMA RecordContextPreservesInv == Inv /\ t_t_record_context => Inv'
BY ConstantsDistinct DEF Inv, t_t_record_context, TypeInvariant, States

LEMMA PauseTracePreservesInv == Inv /\ t_t_pause_trace => Inv'
BY ConstantsDistinct DEF Inv, t_t_pause_trace, TypeInvariant, States

LEMMA ResumeTracePreservesInv == Inv /\ t_t_resume_trace => Inv'
BY ConstantsDistinct DEF Inv, t_t_resume_trace, TypeInvariant, States

LEMMA EndTracePreservesInv == Inv /\ t_t_end_trace => Inv'
BY ConstantsDistinct DEF Inv, t_t_end_trace, TypeInvariant, States

LEMMA EndTracePausedPreservesInv == Inv /\ t_t_end_trace_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_end_trace_paused, TypeInvariant, States

LEMMA FormaotlpPreservesInv == Inv /\ t_t_format_otlp => Inv'
BY ConstantsDistinct DEF Inv, t_t_format_otlp, TypeInvariant, States

LEMMA FormajsonlPreservesInv == Inv /\ t_t_format_jsonl => Inv'
BY ConstantsDistinct DEF Inv, t_t_format_jsonl, TypeInvariant, States

LEMMA FormahumanPreservesInv == Inv /\ t_t_format_human => Inv'
BY ConstantsDistinct DEF Inv, t_t_format_human, TypeInvariant, States

LEMMA FormatimelinePreservesInv == Inv /\ t_t_format_timeline => Inv'
BY ConstantsDistinct DEF Inv, t_t_format_timeline, TypeInvariant, States

LEMMA ExportPreservesInv == Inv /\ t_t_export => Inv'
BY ConstantsDistinct DEF Inv, t_t_export, TypeInvariant, States

LEMMA AnalyzePreservesInv == Inv /\ t_t_analyze => Inv'
BY ConstantsDistinct DEF Inv, t_t_analyze, TypeInvariant, States

LEMMA StatusTracingPreservesInv == Inv /\ t_t_status_tracing => Inv'
BY ConstantsDistinct DEF Inv, t_t_status_tracing, TypeInvariant, States

LEMMA StatusPausedPreservesInv == Inv /\ t_t_status_paused => Inv'
BY ConstantsDistinct DEF Inv, t_t_status_paused, TypeInvariant, States

LEMMA StatusCompletedPreservesInv == Inv /\ t_t_status_completed => Inv'
BY ConstantsDistinct DEF Inv, t_t_status_completed, TypeInvariant, States

LEMMA SeformaconfPreservesInv == Inv /\ t_t_set_format_conf => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_format_conf, TypeInvariant, States

LEMMA SeformacompletedPreservesInv == Inv /\ t_t_set_format_completed => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_format_completed, TypeInvariant, States

LEMMA ClearCompletedPreservesInv == Inv /\ t_t_clear_completed => Inv'
BY ConstantsDistinct DEF Inv, t_t_clear_completed, TypeInvariant, States

LEMMA NewTracePreservesInv == Inv /\ t_t_new_trace => Inv'
BY ConstantsDistinct DEF Inv, t_t_new_trace, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA ResetracingPreservesInv == Inv /\ t_t_reset_tracing => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_tracing, TypeInvariant, States

LEMMA ResecompletedPreservesInv == Inv /\ t_t_reset_completed => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset_completed, TypeInvariant, States

LEMMA RecoverPreservesInv == Inv /\ t_t_recover => Inv'
BY ConstantsDistinct DEF Inv, t_t_recover, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY InitPreservesInv, InierrorPreservesInv, ReconfigurePreservesInv, StartracePreservesInv, StartraceIdlePreservesInv, RecordSpanPreservesInv, StarspanPreservesInv, EndSpanPreservesInv, RecordStatePreservesInv, RecordGatePreservesInv, RecordActionPreservesInv, RecordEventPreservesInv, RecordContextPreservesInv, PauseTracePreservesInv, ResumeTracePreservesInv, EndTracePreservesInv, EndTracePausedPreservesInv, FormaotlpPreservesInv, FormajsonlPreservesInv, FormahumanPreservesInv, FormatimelinePreservesInv, ExportPreservesInv, AnalyzePreservesInv, StatusTracingPreservesInv, StatusPausedPreservesInv, StatusCompletedPreservesInv, SeformaconfPreservesInv, SeformacompletedPreservesInv, ClearCompletedPreservesInv, NewTracePreservesInv, ResetPreservesInv, ResetracingPreservesInv, ResecompletedPreservesInv, RecoverPreservesInv DEF Next

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