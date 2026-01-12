--------------------------- MODULE legacy_extractor_proofs ---------------------------
(*
 * L++ Blueprint: Legacy Code State Machine Extractor
 * Version: 1.0.0
 * TLAPS Mathematical Proof
 *)

EXTENDS Naturals, TLAPS

CONSTANTS
    STATE_idle, STATE_loading, STATE_parsing, STATE_detecting, STATE_extracting_states, STATE_extracting_transitions, STATE_extracting_gates, STATE_extracting_actions, STATE_analyzing_events, STATE_inferring_entry, STATE_generating, STATE_mapping, STATE_complete, STATE_error

ASSUME ConstantsDistinct ==
    /\ STATE_idle /= STATE_loading
    /\ STATE_idle /= STATE_parsing
    /\ STATE_idle /= STATE_detecting
    /\ STATE_idle /= STATE_extracting_states
    /\ STATE_idle /= STATE_extracting_transitions
    /\ STATE_idle /= STATE_extracting_gates
    /\ STATE_idle /= STATE_extracting_actions
    /\ STATE_idle /= STATE_analyzing_events
    /\ STATE_idle /= STATE_inferring_entry
    /\ STATE_idle /= STATE_generating
    /\ STATE_idle /= STATE_mapping
    /\ STATE_idle /= STATE_complete
    /\ STATE_idle /= STATE_error
    /\ STATE_loading /= STATE_parsing
    /\ STATE_loading /= STATE_detecting
    /\ STATE_loading /= STATE_extracting_states
    /\ STATE_loading /= STATE_extracting_transitions
    /\ STATE_loading /= STATE_extracting_gates
    /\ STATE_loading /= STATE_extracting_actions
    /\ STATE_loading /= STATE_analyzing_events
    /\ STATE_loading /= STATE_inferring_entry
    /\ STATE_loading /= STATE_generating
    /\ STATE_loading /= STATE_mapping
    /\ STATE_loading /= STATE_complete
    /\ STATE_loading /= STATE_error
    /\ STATE_parsing /= STATE_detecting
    /\ STATE_parsing /= STATE_extracting_states
    /\ STATE_parsing /= STATE_extracting_transitions
    /\ STATE_parsing /= STATE_extracting_gates
    /\ STATE_parsing /= STATE_extracting_actions
    /\ STATE_parsing /= STATE_analyzing_events
    /\ STATE_parsing /= STATE_inferring_entry
    /\ STATE_parsing /= STATE_generating
    /\ STATE_parsing /= STATE_mapping
    /\ STATE_parsing /= STATE_complete
    /\ STATE_parsing /= STATE_error
    /\ STATE_detecting /= STATE_extracting_states
    /\ STATE_detecting /= STATE_extracting_transitions
    /\ STATE_detecting /= STATE_extracting_gates
    /\ STATE_detecting /= STATE_extracting_actions
    /\ STATE_detecting /= STATE_analyzing_events
    /\ STATE_detecting /= STATE_inferring_entry
    /\ STATE_detecting /= STATE_generating
    /\ STATE_detecting /= STATE_mapping
    /\ STATE_detecting /= STATE_complete
    /\ STATE_detecting /= STATE_error
    /\ STATE_extracting_states /= STATE_extracting_transitions
    /\ STATE_extracting_states /= STATE_extracting_gates
    /\ STATE_extracting_states /= STATE_extracting_actions
    /\ STATE_extracting_states /= STATE_analyzing_events
    /\ STATE_extracting_states /= STATE_inferring_entry
    /\ STATE_extracting_states /= STATE_generating
    /\ STATE_extracting_states /= STATE_mapping
    /\ STATE_extracting_states /= STATE_complete
    /\ STATE_extracting_states /= STATE_error
    /\ STATE_extracting_transitions /= STATE_extracting_gates
    /\ STATE_extracting_transitions /= STATE_extracting_actions
    /\ STATE_extracting_transitions /= STATE_analyzing_events
    /\ STATE_extracting_transitions /= STATE_inferring_entry
    /\ STATE_extracting_transitions /= STATE_generating
    /\ STATE_extracting_transitions /= STATE_mapping
    /\ STATE_extracting_transitions /= STATE_complete
    /\ STATE_extracting_transitions /= STATE_error
    /\ STATE_extracting_gates /= STATE_extracting_actions
    /\ STATE_extracting_gates /= STATE_analyzing_events
    /\ STATE_extracting_gates /= STATE_inferring_entry
    /\ STATE_extracting_gates /= STATE_generating
    /\ STATE_extracting_gates /= STATE_mapping
    /\ STATE_extracting_gates /= STATE_complete
    /\ STATE_extracting_gates /= STATE_error
    /\ STATE_extracting_actions /= STATE_analyzing_events
    /\ STATE_extracting_actions /= STATE_inferring_entry
    /\ STATE_extracting_actions /= STATE_generating
    /\ STATE_extracting_actions /= STATE_mapping
    /\ STATE_extracting_actions /= STATE_complete
    /\ STATE_extracting_actions /= STATE_error
    /\ STATE_analyzing_events /= STATE_inferring_entry
    /\ STATE_analyzing_events /= STATE_generating
    /\ STATE_analyzing_events /= STATE_mapping
    /\ STATE_analyzing_events /= STATE_complete
    /\ STATE_analyzing_events /= STATE_error
    /\ STATE_inferring_entry /= STATE_generating
    /\ STATE_inferring_entry /= STATE_mapping
    /\ STATE_inferring_entry /= STATE_complete
    /\ STATE_inferring_entry /= STATE_error
    /\ STATE_generating /= STATE_mapping
    /\ STATE_generating /= STATE_complete
    /\ STATE_generating /= STATE_error
    /\ STATE_mapping /= STATE_complete
    /\ STATE_mapping /= STATE_error
    /\ STATE_complete /= STATE_error

VARIABLE state

vars == <<state>>

States == {STATE_idle, STATE_loading, STATE_parsing, STATE_detecting, STATE_extracting_states, STATE_extracting_transitions, STATE_extracting_gates, STATE_extracting_actions, STATE_analyzing_events, STATE_inferring_entry, STATE_generating, STATE_mapping, STATE_complete, STATE_error}
TerminalStates == {}

TypeInvariant == state \in States

Init == state = STATE_idle

(* Transition: t_set_mode *)
t_t_set_mode ==
    /\ state = STATE_idle
    /\ state' = STATE_idle

(* Transition: t_start_extract *)
t_t_start_extract ==
    /\ state = STATE_idle
    /\ state' = STATE_loading

(* Transition: t_load_error *)
t_t_load_error ==
    /\ state = STATE_loading
    /\ state' = STATE_error

(* Transition: t_load_done *)
t_t_load_done ==
    /\ state = STATE_loading
    /\ state' = STATE_parsing

(* Transition: t_parse_error *)
t_t_parse_error ==
    /\ state = STATE_parsing
    /\ state' = STATE_error

(* Transition: t_parse_done *)
t_t_parse_done ==
    /\ state = STATE_parsing
    /\ state' = STATE_detecting

(* Transition: t_detect_done *)
t_t_detect_done ==
    /\ state = STATE_detecting
    /\ state' = STATE_extracting_states

(* Transition: t_states_done *)
t_t_states_done ==
    /\ state = STATE_extracting_states
    /\ state' = STATE_extracting_transitions

(* Transition: t_transitions_done *)
t_t_transitions_done ==
    /\ state = STATE_extracting_transitions
    /\ state' = STATE_extracting_gates

(* Transition: t_gates_done *)
t_t_gates_done ==
    /\ state = STATE_extracting_gates
    /\ state' = STATE_extracting_actions

(* Transition: t_actions_done *)
t_t_actions_done ==
    /\ state = STATE_extracting_actions
    /\ state' = STATE_analyzing_events

(* Transition: t_events_done *)
t_t_events_done ==
    /\ state = STATE_analyzing_events
    /\ state' = STATE_inferring_entry

(* Transition: t_entry_done *)
t_t_entry_done ==
    /\ state = STATE_inferring_entry
    /\ state' = STATE_generating

(* Transition: t_generate_done *)
t_t_generate_done ==
    /\ state = STATE_generating
    /\ state' = STATE_mapping

(* Transition: t_mapping_done *)
t_t_mapping_done ==
    /\ state = STATE_mapping
    /\ state' = STATE_complete

(* Transition: t_export_blueprint *)
t_t_export_blueprint ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_export_report *)
t_t_export_report ==
    /\ state = STATE_complete
    /\ state' = STATE_complete

(* Transition: t_reset *)
t_t_reset ==
    /\ state = STATE_complete
    /\ state' = STATE_idle

(* Transition: t_error_reset *)
t_t_error_reset ==
    /\ state = STATE_error
    /\ state' = STATE_idle

Next ==
    \/ t_t_set_mode
    \/ t_t_start_extract
    \/ t_t_load_error
    \/ t_t_load_done
    \/ t_t_parse_error
    \/ t_t_parse_done
    \/ t_t_detect_done
    \/ t_t_states_done
    \/ t_t_transitions_done
    \/ t_t_gates_done
    \/ t_t_actions_done
    \/ t_t_events_done
    \/ t_t_entry_done
    \/ t_t_generate_done
    \/ t_t_mapping_done
    \/ t_t_export_blueprint
    \/ t_t_export_report
    \/ t_t_reset
    \/ t_t_error_reset

Spec == Init /\ [][Next]_vars

Inv == TypeInvariant

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

LEMMA InitEstablishesInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, States

LEMMA SemodePreservesInv == Inv /\ t_t_set_mode => Inv'
BY ConstantsDistinct DEF Inv, t_t_set_mode, TypeInvariant, States

LEMMA StarextractPreservesInv == Inv /\ t_t_start_extract => Inv'
BY ConstantsDistinct DEF Inv, t_t_start_extract, TypeInvariant, States

LEMMA LoadErrorPreservesInv == Inv /\ t_t_load_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_error, TypeInvariant, States

LEMMA LoadDonePreservesInv == Inv /\ t_t_load_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_load_done, TypeInvariant, States

LEMMA ParseErrorPreservesInv == Inv /\ t_t_parse_error => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_error, TypeInvariant, States

LEMMA ParseDonePreservesInv == Inv /\ t_t_parse_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_parse_done, TypeInvariant, States

LEMMA DetecdonePreservesInv == Inv /\ t_t_detect_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_detect_done, TypeInvariant, States

LEMMA StatesDonePreservesInv == Inv /\ t_t_states_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_states_done, TypeInvariant, States

LEMMA TransitionsDonePreservesInv == Inv /\ t_t_transitions_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_transitions_done, TypeInvariant, States

LEMMA GatesDonePreservesInv == Inv /\ t_t_gates_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_gates_done, TypeInvariant, States

LEMMA ActionsDonePreservesInv == Inv /\ t_t_actions_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_actions_done, TypeInvariant, States

LEMMA EventsDonePreservesInv == Inv /\ t_t_events_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_events_done, TypeInvariant, States

LEMMA EntryDonePreservesInv == Inv /\ t_t_entry_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_entry_done, TypeInvariant, States

LEMMA GenerateDonePreservesInv == Inv /\ t_t_generate_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_generate_done, TypeInvariant, States

LEMMA MappingDonePreservesInv == Inv /\ t_t_mapping_done => Inv'
BY ConstantsDistinct DEF Inv, t_t_mapping_done, TypeInvariant, States

LEMMA ExporblueprintPreservesInv == Inv /\ t_t_export_blueprint => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_blueprint, TypeInvariant, States

LEMMA ExporreportPreservesInv == Inv /\ t_t_export_report => Inv'
BY ConstantsDistinct DEF Inv, t_t_export_report, TypeInvariant, States

LEMMA ResetPreservesInv == Inv /\ t_t_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_reset, TypeInvariant, States

LEMMA ErrorResetPreservesInv == Inv /\ t_t_error_reset => Inv'
BY ConstantsDistinct DEF Inv, t_t_error_reset, TypeInvariant, States

LEMMA StutterPreservesInv == Inv /\ UNCHANGED vars => Inv'
BY DEF Inv, vars, TypeInvariant

LEMMA NextPreservesInv == Inv /\ Next => Inv'
BY SemodePreservesInv, StarextractPreservesInv, LoadErrorPreservesInv, LoadDonePreservesInv, ParseErrorPreservesInv, ParseDonePreservesInv, DetecdonePreservesInv, StatesDonePreservesInv, TransitionsDonePreservesInv, GatesDonePreservesInv, ActionsDonePreservesInv, EventsDonePreservesInv, EntryDonePreservesInv, GenerateDonePreservesInv, MappingDonePreservesInv, ExporblueprintPreservesInv, ExporreportPreservesInv, ResetPreservesInv, ErrorResetPreservesInv DEF Next

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