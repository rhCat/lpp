---------------------------- MODULE lpp_visualizer ----------------------------
\* L++ Blueprint: L++ Blueprint Visualizer
\* Version: 1.0.0
\* Auto-generated TLA+ specification (universal adaptor)

EXTENDS Integers, Sequences, TLC

\* =========================================================
\* BOUNDS - Constrain state space for model checking
\* =========================================================
INT_MIN == -1
INT_MAX == 1
MAX_HISTORY == 2
BoundedInt == INT_MIN..INT_MAX

\* NULL constant for uninitialized values
CONSTANT NULL

\* States
States == {"idle", "loaded", "viewing", "exporting", "error"}

Events == {"BACK", "CLEAR", "DESELECT", "EXPORT_README", "LOAD", "LOAD_FAILED", "SELECT", "TOGGLE_ACTIONS", "TOGGLE_GATES", "UNLOAD", "VIEW", "VIEW_GRAPH", "VIEW_MERMAID", "VIEW_TABLE", "ZOOM_IN", "ZOOM_OUT"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    blueprint,           \* The loaded Blueprint object
    blueprint_name,           \* Blueprint name (flattened for display)
    blueprint_id,           \* Blueprint ID (flattened for display)
    view_mode,           \* Current view: 'graph' | 'table' | 'mermaid'
    selected_node,           \* Currently selected state/transition ID
    zoom_level,           \* Zoom level 0.5 - 2.0
    show_gates,           \* Whether to show gate expressions
    show_actions,           \* Whether to show action details
    output,           \* Generated visualization output
    readme_content,           \* Generated README markdown content
    export_path,           \* Path where README was exported
    error,           \* Error message if any
    event_history    \* Trace of events

vars == <<state, blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprint_name: any string or NULL
    /\ TRUE  \* blueprint_id: any string or NULL
    /\ TRUE  \* view_mode: any string or NULL
    /\ TRUE  \* selected_node: any string or NULL
    /\ (zoom_level \in BoundedInt) \/ (zoom_level = NULL)
    /\ (show_gates \in BOOLEAN) \/ (show_gates = NULL)
    /\ (show_actions \in BOOLEAN) \/ (show_actions = NULL)
    /\ TRUE  \* output: any string or NULL
    /\ TRUE  \* readme_content: any string or NULL
    /\ TRUE  \* export_path: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (zoom_level = NULL) \/ (zoom_level \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint = NULL
    /\ blueprint_name = NULL
    /\ blueprint_id = NULL
    /\ view_mode = NULL
    /\ selected_node = NULL
    /\ zoom_level = NULL
    /\ show_gates = NULL
    /\ show_actions = NULL
    /\ output = NULL
    /\ readme_content = NULL
    /\ export_path = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_load: idle --(LOAD)--> loaded
t_load ==
    /\ state = "idle"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_load_error: idle --(LOAD_FAILED)--> error
t_load_error ==
    /\ state = "idle"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD_FAILED")

\* t_reload: loaded --(LOAD)--> loaded
t_reload ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_reload_from_viewing: viewing --(LOAD)--> loaded
t_reload_from_viewing ==
    /\ state = "viewing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_start_view: loaded --(VIEW)--> viewing
t_start_view ==
    /\ state = "loaded"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "VIEW")

\* t_switch_to_graph: viewing --(VIEW_GRAPH)--> viewing
t_switch_to_graph ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "VIEW_GRAPH")

\* t_switch_to_table: viewing --(VIEW_TABLE)--> viewing
t_switch_to_table ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "VIEW_TABLE")

\* t_switch_to_mermaid: viewing --(VIEW_MERMAID)--> viewing
t_switch_to_mermaid ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "VIEW_MERMAID")

\* t_select: viewing --(SELECT)--> viewing
t_select ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "SELECT")

\* t_deselect: viewing --(DESELECT)--> viewing
t_deselect ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DESELECT")

\* t_zoom_in: viewing --(ZOOM_IN)--> viewing
t_zoom_in ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "ZOOM_IN")

\* t_zoom_out: viewing --(ZOOM_OUT)--> viewing
t_zoom_out ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "ZOOM_OUT")

\* t_toggle_gates: viewing --(TOGGLE_GATES)--> viewing
t_toggle_gates ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "TOGGLE_GATES")

\* t_toggle_actions: viewing --(TOGGLE_ACTIONS)--> viewing
t_toggle_actions ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "TOGGLE_ACTIONS")

\* t_back_to_loaded: viewing --(BACK)--> loaded
t_back_to_loaded ==
    /\ state = "viewing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "BACK")

\* t_unload: loaded --(UNLOAD)--> idle
t_unload ==
    /\ state = "loaded"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_unload_from_viewing: viewing --(UNLOAD)--> idle
t_unload_from_viewing ==
    /\ state = "viewing"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "UNLOAD")

\* t_export_readme_from_loaded: loaded --(EXPORT_README)--> loaded
t_export_readme_from_loaded ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT_README")

\* t_export_readme_from_viewing: viewing --(EXPORT_README)--> viewing
t_export_readme_from_viewing ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "EXPORT_README")

\* t_recover: error --(CLEAR)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_name' = blueprint_name
    /\ blueprint_id' = blueprint_id
    /\ view_mode' = view_mode
    /\ selected_node' = selected_node
    /\ zoom_level' = zoom_level
    /\ show_gates' = show_gates
    /\ show_actions' = show_actions
    /\ output' = output
    /\ readme_content' = readme_content
    /\ export_path' = export_path
    /\ error' = error
    /\ event_history' = Append(event_history, "CLEAR")

\* Next state relation
Next ==
    \/ t_load
    \/ t_load_error
    \/ t_reload
    \/ t_reload_from_viewing
    \/ t_start_view
    \/ t_switch_to_graph
    \/ t_switch_to_table
    \/ t_switch_to_mermaid
    \/ t_select
    \/ t_deselect
    \/ t_zoom_in
    \/ t_zoom_out
    \/ t_toggle_gates
    \/ t_toggle_actions
    \/ t_back_to_loaded
    \/ t_unload
    \/ t_unload_from_viewing
    \/ t_export_readme_from_loaded
    \/ t_export_readme_from_viewing
    \/ t_recover

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================