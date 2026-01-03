---------------------------- MODULE lpp_blueprint_differ ----------------------------
\* L++ Blueprint: L++ Blueprint Diff & Merge
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
States == {"idle", "left_loaded", "ready", "diffing", "diff_complete", "merging", "merge_complete", "conflict", "error"}

Events == {"BACK", "CLEAR", "CONFLICT_DETECTED", "DIFF", "DIFF_ALL", "DIFF_DONE", "EXPORT", "LOAD_BASE", "LOAD_FAILED", "LOAD_LEFT", "LOAD_RIGHT", "MERGE", "MERGE_AUTO", "MERGE_LEFT", "MERGE_RIGHT", "RESET", "SHOW_PATCH", "SHOW_SUMMARY", "SHOW_UNIFIED", "TAKE_LEFT", "TAKE_RIGHT"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    blueprint_left,           \* First blueprint (left/base) for comparison
    blueprint_right,           \* Second blueprint (right/target) for comparison
    blueprint_base,           \* Common ancestor blueprint for 3-way merge
    path_left,           \* Path to left blueprint file
    path_right,           \* Path to right blueprint file
    path_base,           \* Path to base blueprint file
    diff_result,           \* Computed semantic diff between blueprints
    conflicts,           \* List of detected merge conflicts
    merged_blueprint,           \* Result of merge operation
    merge_strategy,           \* Merge strategy: take_left, take_right, manual
    diff_format,           \* Output format: unified, summary, json_patch
    formatted_diff,           \* Formatted diff output for display
    json_patch,           \* RFC 6902 JSON patch operations
    export_path,           \* Path where merged blueprint was exported
    error,           \* Error message if any
    event_history    \* Trace of events

vars == <<state, blueprint_left, blueprint_right, blueprint_base, path_left, path_right, path_base, diff_result, conflicts, merged_blueprint, merge_strategy, diff_format, formatted_diff, json_patch, export_path, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint_left: any string or NULL
    /\ TRUE  \* blueprint_right: any string or NULL
    /\ TRUE  \* blueprint_base: any string or NULL
    /\ TRUE  \* path_left: any string or NULL
    /\ TRUE  \* path_right: any string or NULL
    /\ TRUE  \* path_base: any string or NULL
    /\ TRUE  \* diff_result: any string or NULL
    /\ TRUE  \* conflicts: any string or NULL
    /\ TRUE  \* merged_blueprint: any string or NULL
    /\ TRUE  \* merge_strategy: any string or NULL
    /\ TRUE  \* diff_format: any string or NULL
    /\ TRUE  \* formatted_diff: any string or NULL
    /\ TRUE  \* json_patch: any string or NULL
    /\ TRUE  \* export_path: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint_left = NULL
    /\ blueprint_right = NULL
    /\ blueprint_base = NULL
    /\ path_left = NULL
    /\ path_right = NULL
    /\ path_base = NULL
    /\ diff_result = NULL
    /\ conflicts = NULL
    /\ merged_blueprint = NULL
    /\ merge_strategy = NULL
    /\ diff_format = NULL
    /\ formatted_diff = NULL
    /\ json_patch = NULL
    /\ export_path = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_load_left_from_idle: idle --(LOAD_LEFT)--> left_loaded
t_load_left_from_idle ==
    /\ state = "idle"
    /\ state' = "left_loaded"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_LEFT")

\* t_load_right_from_left: left_loaded --(LOAD_RIGHT)--> ready
t_load_right_from_left ==
    /\ state = "left_loaded"
    /\ state' = "ready"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_RIGHT")

\* t_load_base_from_ready: ready --(LOAD_BASE)--> ready
t_load_base_from_ready ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_BASE")

\* t_reload_left: ready --(LOAD_LEFT)--> ready
t_reload_left ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_LEFT")

\* t_reload_right: ready --(LOAD_RIGHT)--> ready
t_reload_right ==
    /\ state = "ready"
    /\ state' = "ready"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_RIGHT")

\* t_start_diff: ready --(DIFF)--> diffing
t_start_diff ==
    /\ state = "ready"
    /\ blueprint_left /= NULL /\ blueprint_right /= NULL  \* gate: has_both
    /\ state' = "diffing"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DIFF")

\* t_diff_to_complete: diffing --(DIFF_DONE)--> diff_complete
t_diff_to_complete ==
    /\ state = "diffing"
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DIFF_DONE")

\* t_auto_diff_complete: ready --(DIFF_ALL)--> diff_complete
t_auto_diff_complete ==
    /\ state = "ready"
    /\ blueprint_left /= NULL /\ blueprint_right /= NULL  \* gate: has_both
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DIFF_ALL")

\* t_show_summary: diff_complete --(SHOW_SUMMARY)--> diff_complete
t_show_summary ==
    /\ state = "diff_complete"
    /\ diff_result /= NULL  \* gate: has_diff
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "SHOW_SUMMARY")

\* t_show_unified: diff_complete --(SHOW_UNIFIED)--> diff_complete
t_show_unified ==
    /\ state = "diff_complete"
    /\ diff_result /= NULL  \* gate: has_diff
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "SHOW_UNIFIED")

\* t_show_patch: diff_complete --(SHOW_PATCH)--> diff_complete
t_show_patch ==
    /\ state = "diff_complete"
    /\ diff_result /= NULL  \* gate: has_diff
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "SHOW_PATCH")

\* t_start_merge: diff_complete --(MERGE)--> merging
t_start_merge ==
    /\ state = "diff_complete"
    /\ diff_result /= NULL  \* gate: has_diff
    /\ state' = "merging"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "MERGE")

\* t_merge_no_conflict: merging --(MERGE_AUTO)--> merge_complete
t_merge_no_conflict ==
    /\ state = "merging"
    /\ conflicts = NULL \/ Len(conflicts) = 0  \* gate: no_conflicts
    /\ state' = "merge_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "MERGE_AUTO")

\* t_merge_conflict_detected: merging --(CONFLICT_DETECTED)--> conflict
t_merge_conflict_detected ==
    /\ state = "merging"
    /\ conflicts /= NULL /\ Len(conflicts) > 0  \* gate: has_conflicts
    /\ state' = "conflict"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CONFLICT_DETECTED")

\* t_resolve_take_left: conflict --(TAKE_LEFT)--> merge_complete
t_resolve_take_left ==
    /\ state = "conflict"
    /\ state' = "merge_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "TAKE_LEFT")

\* t_resolve_take_right: conflict --(TAKE_RIGHT)--> merge_complete
t_resolve_take_right ==
    /\ state = "conflict"
    /\ state' = "merge_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "TAKE_RIGHT")

\* t_force_merge_left: diff_complete --(MERGE_LEFT)--> merge_complete
t_force_merge_left ==
    /\ state = "diff_complete"
    /\ diff_result /= NULL  \* gate: has_diff
    /\ state' = "merge_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "MERGE_LEFT")

\* t_force_merge_right: diff_complete --(MERGE_RIGHT)--> merge_complete
t_force_merge_right ==
    /\ state = "diff_complete"
    /\ diff_result /= NULL  \* gate: has_diff
    /\ state' = "merge_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "MERGE_RIGHT")

\* t_export: merge_complete --(EXPORT)--> merge_complete
t_export ==
    /\ state = "merge_complete"
    /\ merged_blueprint /= NULL  \* gate: has_merged
    /\ state' = "merge_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT")

\* t_back_to_diff: merge_complete --(BACK)--> diff_complete
t_back_to_diff ==
    /\ state = "merge_complete"
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_back_from_conflict: conflict --(BACK)--> diff_complete
t_back_from_conflict ==
    /\ state = "conflict"
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_rediff: diff_complete --(DIFF_ALL)--> diff_complete
t_rediff ==
    /\ state = "diff_complete"
    /\ state' = "diff_complete"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DIFF_ALL")

\* t_back_to_ready: diff_complete --(RESET)--> ready
t_back_to_ready ==
    /\ state = "diff_complete"
    /\ state' = "ready"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t_clear_all: ready --(CLEAR)--> idle
t_clear_all ==
    /\ state = "ready"
    /\ state' = "idle"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_clear_from_diff: diff_complete --(CLEAR)--> idle
t_clear_from_diff ==
    /\ state = "diff_complete"
    /\ state' = "idle"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_clear_from_merge: merge_complete --(CLEAR)--> idle
t_clear_from_merge ==
    /\ state = "merge_complete"
    /\ state' = "idle"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_error_recover: error --(CLEAR)--> idle
t_error_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* t_load_error: * --(LOAD_FAILED)--> error
t_load_error ==
    /\ TRUE  \* from any state
    /\ state' = "error"
    /\ blueprint_left' = blueprint_left
    /\ blueprint_right' = blueprint_right
    /\ blueprint_base' = blueprint_base
    /\ path_left' = path_left
    /\ path_right' = path_right
    /\ path_base' = path_base
    /\ diff_result' = diff_result
    /\ conflicts' = conflicts
    /\ merged_blueprint' = merged_blueprint
    /\ merge_strategy' = merge_strategy
    /\ diff_format' = diff_format
    /\ formatted_diff' = formatted_diff
    /\ json_patch' = json_patch
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_FAILED")

\* Next state relation
Next ==
    \/ t_load_left_from_idle
    \/ t_load_right_from_left
    \/ t_load_base_from_ready
    \/ t_reload_left
    \/ t_reload_right
    \/ t_start_diff
    \/ t_diff_to_complete
    \/ t_auto_diff_complete
    \/ t_show_summary
    \/ t_show_unified
    \/ t_show_patch
    \/ t_start_merge
    \/ t_merge_no_conflict
    \/ t_merge_conflict_detected
    \/ t_resolve_take_left
    \/ t_resolve_take_right
    \/ t_force_merge_left
    \/ t_force_merge_right
    \/ t_export
    \/ t_back_to_diff
    \/ t_back_from_conflict
    \/ t_rediff
    \/ t_back_to_ready
    \/ t_clear_all
    \/ t_clear_from_diff
    \/ t_clear_from_merge
    \/ t_error_recover
    \/ t_load_error

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================