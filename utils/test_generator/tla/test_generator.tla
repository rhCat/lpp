---------------------------- MODULE test_generator ----------------------------
\* L++ Blueprint: L++ Test Case Generator
\* Version: 1.0.0
\* Auto-generated TLA+ specification (universal adaptor)

EXTENDS Integers, Sequences, TLC

\* =========================================================
\* BOUNDS - Constrain state space for model checking
\* =========================================================
INT_MIN == -5
INT_MAX == 5
MAX_HISTORY == 3
BoundedInt == INT_MIN..INT_MAX

\* NULL constant for uninitialized values
CONSTANT NULL

\* States
States == {"idle", "loaded", "analyzing", "generating", "complete", "exporting", "error"}

Events == {"ANALYZE", "AUTO", "BACK", "COMBINE", "COVERAGE", "ERROR", "EXPORT", "FORMAT_JSON", "FORMAT_PYTEST", "GENERATE", "GENERATE_ALL", "LOAD", "RESET"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    blueprint,           \* The loaded blueprint to generate tests for
    blueprint_path,           \* Path to the loaded blueprint file
    graph,           \* Adjacency graph of states and transitions
    paths,           \* All discovered paths through the state machine
    gate_analysis,           \* Boundary conditions extracted from gates
    path_tests,           \* Generated path coverage tests
    state_tests,           \* Generated state coverage tests
    gate_tests,           \* Generated gate boundary tests
    negative_tests,           \* Generated negative/invalid input tests
    property_tests,           \* Generated property-based tests
    all_tests,           \* Combined test suite
    output_format,           \* Export format: json | pytest
    output_path,           \* Path where tests were exported
    formatted_output,           \* Formatted test output string
    coverage_report,           \* Coverage analysis report
    error,           \* Error message if any
    event_history    \* Trace of events

vars == <<state, blueprint, blueprint_path, graph, paths, gate_analysis, path_tests, state_tests, gate_tests, negative_tests, property_tests, all_tests, output_format, output_path, formatted_output, coverage_report, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprint_path: any string or NULL
    /\ TRUE  \* graph: any string or NULL
    /\ TRUE  \* paths: any string or NULL
    /\ TRUE  \* gate_analysis: any string or NULL
    /\ TRUE  \* path_tests: any string or NULL
    /\ TRUE  \* state_tests: any string or NULL
    /\ TRUE  \* gate_tests: any string or NULL
    /\ TRUE  \* negative_tests: any string or NULL
    /\ TRUE  \* property_tests: any string or NULL
    /\ TRUE  \* all_tests: any string or NULL
    /\ TRUE  \* output_format: any string or NULL
    /\ TRUE  \* output_path: any string or NULL
    /\ TRUE  \* formatted_output: any string or NULL
    /\ TRUE  \* coverage_report: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint = NULL
    /\ blueprint_path = NULL
    /\ graph = NULL
    /\ paths = NULL
    /\ gate_analysis = NULL
    /\ path_tests = NULL
    /\ state_tests = NULL
    /\ gate_tests = NULL
    /\ negative_tests = NULL
    /\ property_tests = NULL
    /\ all_tests = NULL
    /\ output_format = NULL
    /\ output_path = NULL
    /\ formatted_output = NULL
    /\ coverage_report = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_load: idle --(LOAD)--> loaded
t_load ==
    /\ state = "idle"
    /\ blueprint = NULL  \* gate: no_blueprint
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_reload: loaded --(LOAD)--> loaded
t_reload ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_reload_from_complete: complete --(LOAD)--> loaded
t_reload_from_complete ==
    /\ state = "complete"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_analyze: loaded --(ANALYZE)--> analyzing
t_analyze ==
    /\ state = "loaded"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "analyzing"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "ANALYZE")

\* t_generate_all: analyzing --(GENERATE)--> generating
t_generate_all ==
    /\ state = "analyzing"
    /\ paths /= NULL /\ Len(paths) > 0  \* gate: has_paths
    /\ state' = "generating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE")

\* t_generate_from_loaded: loaded --(GENERATE_ALL)--> generating
t_generate_from_loaded ==
    /\ state = "loaded"
    /\ blueprint /= NULL  \* gate: has_blueprint
    /\ state' = "generating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE_ALL")

\* t_combine: generating --(COMBINE)--> complete
t_combine ==
    /\ state = "generating"
    /\ path_tests /= NULL  \* gate: has_path_tests
    /\ state' = "complete"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "COMBINE")

\* t_auto_combine: generating --(AUTO)--> complete
t_auto_combine ==
    /\ state = "generating"
    /\ path_tests /= NULL  \* gate: has_path_tests
    /\ state' = "complete"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "AUTO")

\* t_format_json: complete --(FORMAT_JSON)--> complete
t_format_json ==
    /\ state = "complete"
    /\ all_tests /= NULL /\ Len(all_tests) > 0  \* gate: has_tests
    /\ state' = "complete"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "FORMAT_JSON")

\* t_format_pytest: complete --(FORMAT_PYTEST)--> complete
t_format_pytest ==
    /\ state = "complete"
    /\ all_tests /= NULL /\ Len(all_tests) > 0  \* gate: has_tests
    /\ state' = "complete"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "FORMAT_PYTEST")

\* t_export: complete --(EXPORT)--> complete
t_export ==
    /\ state = "complete"
    /\ formatted_output /= NULL  \* gate: has_output
    /\ state' = "complete"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT")

\* t_view_coverage: complete --(COVERAGE)--> complete
t_view_coverage ==
    /\ state = "complete"
    /\ all_tests /= NULL /\ Len(all_tests) > 0  \* gate: has_tests
    /\ state' = "complete"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "COVERAGE")

\* t_reset: complete --(RESET)--> idle
t_reset ==
    /\ state = "complete"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t_reset_from_error: error --(RESET)--> idle
t_reset_from_error ==
    /\ state = "error"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t_error_load: idle --(ERROR)--> error
t_error_load ==
    /\ state = "idle"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t_error_analyze: analyzing --(ERROR)--> error
t_error_analyze ==
    /\ state = "analyzing"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t_error_generate: generating --(ERROR)--> error
t_error_generate ==
    /\ state = "generating"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t_back_to_loaded: analyzing --(BACK)--> loaded
t_back_to_loaded ==
    /\ state = "analyzing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_back_from_complete: complete --(BACK)--> loaded
t_back_from_complete ==
    /\ state = "complete"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ graph' = graph
    /\ paths' = paths
    /\ gate_analysis' = gate_analysis
    /\ path_tests' = path_tests
    /\ state_tests' = state_tests
    /\ gate_tests' = gate_tests
    /\ negative_tests' = negative_tests
    /\ property_tests' = property_tests
    /\ all_tests' = all_tests
    /\ output_format' = output_format
    /\ output_path' = output_path
    /\ formatted_output' = formatted_output
    /\ coverage_report' = coverage_report
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* Next state relation
Next ==
    \/ t_load
    \/ t_reload
    \/ t_reload_from_complete
    \/ t_analyze
    \/ t_generate_all
    \/ t_generate_from_loaded
    \/ t_combine
    \/ t_auto_combine
    \/ t_format_json
    \/ t_format_pytest
    \/ t_export
    \/ t_view_coverage
    \/ t_reset
    \/ t_reset_from_error
    \/ t_error_load
    \/ t_error_analyze
    \/ t_error_generate
    \/ t_back_to_loaded
    \/ t_back_from_complete

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================