# L++ Blueprint Analysis Report

**Generated:** 2026-01-03 14:36:04

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total Blueprints | 26 |
| Total States | 186 |
| Total Transitions | 590 |
| Total Gates | 293 |
| Total Actions | 448 |
| Avg Cyclomatic Complexity | 17.54 |

### Lint Summary

| Severity | Count |
|----------|-------|
| Errors | 0 |
| Warnings | 24 |
| Info | 242 |

### Compliance Summary

| Metric | Value |
|--------|-------|
| Checks Passed | 53 |
| Checks Failed | 29 |
| Compliance Rate | 64.6% |

## Per-Tool Status

| Tool | Version | States | Transitions | Complexity | Lint Status | Compliance |
|------|---------|--------|-------------|------------|------------|------------|
| blueprint_composer | 1.0.0 | 8 | 28 | 22 | PASS | 0% |
| blueprint_debugger | 1.0.0 | 7 | 49 | 44 | W:4 | 100% |
| blueprint_differ | 1.0.0 | 9 | 28 | 21 | PASS | 100% |
| blueprint_linter | 1.0.0 | 5 | 24 | 21 | PASS | 100% |
| blueprint_playground | 1.0.0 | 6 | 21 | 17 | W:4 | 0% |
| blueprint_registry | 1.0.0 | 6 | 29 | 25 | PASS | 0% |
| compliance_checker | 1.0.0 | 6 | 23 | 19 | PASS | 100% |
| coverage_analyzer | 1.0.0 | 6 | 37 | 33 | PASS | 0% |
| doc_generator | 1.0.0 | 7 | 24 | 19 | PASS | 100% |
| event_simulator | 1.0.0 | 7 | 26 | 21 | W:6 | 0% |
| execution_tracer | 1.0.0 | 8 | 34 | 28 | W:4 | 100% |
| function_decoder | 1.0.0 | 7 | 10 | 5 | PASS | 100% |
| graph_visualizer | 1.0.0 | 3 | 2 | 1 | PASS | 100% |
| legacy_extractor | 1.0.0 | 14 | 19 | 7 | PASS | 100% |
| llm_assistant | 1.0.0 | 4 | 13 | 11 | PASS | 100% |
| logic_decoder | 1.0.0 | 7 | 10 | 5 | PASS | 0% |
| research_scraper | 1.0.1 | 3 | 9 | 8 | W:1 | 100% |
| schema_migrator | 1.0.0 | 9 | 29 | 22 | PASS | 100% |
| scholar_chat | 1.0.0 | 6 | 13 | 9 | PASS | 100% |
| skill_contractor | 1.7.0 | 13 | 59 | 48 | PASS | 0% |
| skill_registry | 1.0.0 | 4 | 9 | 7 | W:1 | 100% |
| task_orchestrator | 2.0.0 | 11 | 28 | 19 | PASS | 0% |
| test_generator | 1.0.0 | 7 | 19 | 14 | W:2 | 100% |
| tlaps_seal | 1.0.0 | 10 | 14 | 6 | PASS | 0% |
| visualizer | 1.1.0 | 5 | 26 | 23 | W:2 | 100% |
| visualizer | 1.0.0 | 8 | 7 | 1 | PASS | 100% |

## Lint Findings

### Warnings

- **blueprint_debugger** [L001]: State 'inspecting' has no incoming transitions
  - Suggestion: Add a transition to 'inspecting' or remove it
- **blueprint_debugger** [L001]: State 'time_travel' has no incoming transitions
  - Suggestion: Add a transition to 'time_travel' or remove it
- **blueprint_debugger** [L002]: Non-terminal state 'inspecting' has no outgoing transitions
  - Suggestion: Add transitions from 'inspecting', mark as terminal, or use wildcard transition
- **blueprint_debugger** [L002]: Non-terminal state 'time_travel' has no outgoing transitions
  - Suggestion: Add transitions from 'time_travel', mark as terminal, or use wildcard transition
- **blueprint_playground** [L001]: State 'serving' has no incoming transitions
  - Suggestion: Add a transition to 'serving' or remove it
- **blueprint_playground** [L001]: State 'validating' has no incoming transitions
  - Suggestion: Add a transition to 'validating' or remove it
- **blueprint_playground** [L002]: Non-terminal state 'serving' has no outgoing transitions
  - Suggestion: Add transitions from 'serving', mark as terminal, or use wildcard transition
- **blueprint_playground** [L002]: Non-terminal state 'validating' has no outgoing transitions
  - Suggestion: Add transitions from 'validating', mark as terminal, or use wildcard transition
- **event_simulator** [L001]: State 'exploring' has no incoming transitions
  - Suggestion: Add a transition to 'exploring' or remove it
- **event_simulator** [L001]: State 'fuzzing' has no incoming transitions
  - Suggestion: Add a transition to 'fuzzing' or remove it
- **event_simulator** [L001]: State 'sequence_running' has no incoming transitions
  - Suggestion: Add a transition to 'sequence_running' or remove it
- **event_simulator** [L002]: Non-terminal state 'exploring' has no outgoing transitions
  - Suggestion: Add transitions from 'exploring', mark as terminal, or use wildcard transition
- **event_simulator** [L002]: Non-terminal state 'fuzzing' has no outgoing transitions
  - Suggestion: Add transitions from 'fuzzing', mark as terminal, or use wildcard transition
- **event_simulator** [L002]: Non-terminal state 'sequence_running' has no outgoing transitions
  - Suggestion: Add transitions from 'sequence_running', mark as terminal, or use wildcard transition
- **execution_tracer** [L001]: State 'analyzing' has no incoming transitions
  - Suggestion: Add a transition to 'analyzing' or remove it
- **execution_tracer** [L001]: State 'exporting' has no incoming transitions
  - Suggestion: Add a transition to 'exporting' or remove it
- **execution_tracer** [L002]: Non-terminal state 'analyzing' has no outgoing transitions
  - Suggestion: Add transitions from 'analyzing', mark as terminal, or use wildcard transition
- **execution_tracer** [L002]: Non-terminal state 'exporting' has no outgoing transitions
  - Suggestion: Add transitions from 'exporting', mark as terminal, or use wildcard transition
- **research_scraper** [L001]: State 'error' has no incoming transitions
  - Suggestion: Add a transition to 'error' or remove it
- **skill_registry** [L001]: State 'error' has no incoming transitions
  - Suggestion: Add a transition to 'error' or remove it
- **test_generator** [L001]: State 'exporting' has no incoming transitions
  - Suggestion: Add a transition to 'exporting' or remove it
- **test_generator** [L002]: Non-terminal state 'exporting' has no outgoing transitions
  - Suggestion: Add transitions from 'exporting', mark as terminal, or use wildcard transition
- **visualizer** [L001]: State 'exporting' has no incoming transitions
  - Suggestion: Add a transition to 'exporting' or remove it
- **visualizer** [L002]: Non-terminal state 'exporting' has no outgoing transitions
  - Suggestion: Add transitions from 'exporting', mark as terminal, or use wildcard transition

## Compliance Issues

- **blueprint_composer** [DATA-001]: Transition 't_save_manifest' (SAVE_MANIFEST) missing required gate matching '.*valid.*|.*is_valid.*|.*has_data.*|.*can_save.*'
  - Fix: Add a gate matching '.*valid.*|.*is_valid.*|.*has_data.*|.*can_save.*' to transition 't_save_manifest'
- **blueprint_playground** [AUD-001]: Transition 't_update' (UPDATE) missing required action matching '.*log.*|.*audit.*|.*record.*|.*track.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*record.*|.*track.*' to transition 't_update'
- **blueprint_playground** [DATA-001]: Gate 'is_valid_json' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'is_valid_json' expression to include pattern matching 'is not None|!= None|is None'
- **blueprint_playground** [DATA-001]: Gate 'is_invalid_json' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'is_invalid_json' expression to include pattern matching 'is not None|!= None|is None'
- **blueprint_playground** [DATA-001]: Gate 'is_valid_blueprint' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'is_valid_blueprint' expression to include pattern matching 'is not None|!= None|is None'
- **blueprint_playground** [SEC-001]: Transition 't_update' (UPDATE) missing required gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*'
  - Fix: Add a gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*' to transition 't_update'
- **blueprint_registry** [AUD-001]: Transition 't_delete' (DELETE) missing required action matching '.*log.*|.*audit.*|.*record.*|.*track.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*record.*|.*track.*' to transition 't_delete'
- **blueprint_registry** [AUD-001]: Transition 't_delete_from_ready' (DELETE) missing required action matching '.*log.*|.*audit.*|.*record.*|.*track.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*record.*|.*track.*' to transition 't_delete_from_ready'
- **blueprint_registry** [AUD-001]: Transition 't_update' (UPDATE) missing required action matching '.*log.*|.*audit.*|.*record.*|.*track.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*record.*|.*track.*' to transition 't_update'
- **blueprint_registry** [AUD-001]: Transition 't_update_from_viewing' (UPDATE) missing required action matching '.*log.*|.*audit.*|.*record.*|.*track.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*record.*|.*track.*' to transition 't_update_from_viewing'
- **blueprint_registry** [SEC-001]: Transition 't_delete' (DELETE) missing required gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*'
  - Fix: Add a gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*' to transition 't_delete'
- **blueprint_registry** [SEC-001]: Transition 't_delete_from_ready' (DELETE) missing required gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*'
  - Fix: Add a gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*' to transition 't_delete_from_ready'
- **blueprint_registry** [SEC-001]: Transition 't_update' (UPDATE) missing required gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*'
  - Fix: Add a gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*' to transition 't_update'
- **blueprint_registry** [SEC-001]: Transition 't_update_from_viewing' (UPDATE) missing required gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*'
  - Fix: Add a gate matching '.*auth.*|.*authenticated.*|.*is_admin.*|.*has_permission.*' to transition 't_update_from_viewing'
- **coverage_analyzer** [DATA-001]: Transition 't_import_trace_loaded' (IMPORT) missing required gate matching '.*valid.*|.*is_valid.*|.*can_import.*'
  - Fix: Add a gate matching '.*valid.*|.*is_valid.*|.*can_import.*' to transition 't_import_trace_loaded'
- **coverage_analyzer** [DATA-001]: Transition 't_import_trace_tracking' (IMPORT) missing required gate matching '.*valid.*|.*is_valid.*|.*can_import.*'
  - Fix: Add a gate matching '.*valid.*|.*is_valid.*|.*can_import.*' to transition 't_import_trace_tracking'
- **event_simulator** [DATA-001]: Transition 't_import' (IMPORT) missing required gate matching '.*valid.*|.*is_valid.*|.*can_import.*'
  - Fix: Add a gate matching '.*valid.*|.*is_valid.*|.*can_import.*' to transition 't_import'
- **logic_decoder** [AUD-001]: Transition 't6_error_parse' (ERROR) missing required action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*' to transition 't6_error_parse'
- **logic_decoder** [AUD-001]: Transition 't7_error_analyze' (ERROR) missing required action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*' to transition 't7_error_analyze'
- **logic_decoder** [AUD-001]: Transition 't8_error_infer' (ERROR) missing required action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*' to transition 't8_error_infer'
- **skill_contractor** [DATA-001]: Gate 'lpp_valid' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'lpp_valid' expression to include pattern matching 'is not None|!= None|is None'
- **skill_contractor** [DATA-001]: Gate 'lpp_invalid' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'lpp_invalid' expression to include pattern matching 'is not None|!= None|is None'
- **skill_contractor** [DATA-001]: Gate 'blueprint_validated' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'blueprint_validated' expression to include pattern matching 'is not None|!= None|is None'
- **skill_contractor** [DATA-001]: Gate 'blueprint_not_validated' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'blueprint_not_validated' expression to include pattern matching 'is not None|!= None|is None'
- **skill_contractor** [DATA-001]: Gate 'interactive_valid' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'interactive_valid' expression to include pattern matching 'is not None|!= None|is None'
- **skill_contractor** [DATA-001]: Gate 'interactive_invalid' expression missing required pattern 'is not None|!= None|is None'
  - Fix: Update gate 'interactive_invalid' expression to include pattern matching 'is not None|!= None|is None'
- **skill_contractor** [WF-001]: Transition 't_submit_target' (SUBMIT) missing required gate matching '.*valid.*|.*complete.*|.*can_submit.*'
  - Fix: Add a gate matching '.*valid.*|.*complete.*|.*can_submit.*' to transition 't_submit_target'
- **task_orchestrator** [WF-001]: Transition 't_submit' (SUBMIT) missing required gate matching '.*valid.*|.*complete.*|.*can_submit.*'
  - Fix: Add a gate matching '.*valid.*|.*complete.*|.*can_submit.*' to transition 't_submit'
- **tlaps_seal** [AUD-001]: Transition 't12_error_any' (ERROR) missing required action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*'
  - Fix: Add an action matching '.*log.*|.*audit.*|.*set_error.*|.*record.*' to transition 't12_error_any'

---

_Generated by L++ Utils Inspection_
