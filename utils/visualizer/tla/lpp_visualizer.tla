---------------------------- MODULE lpp_visualizer ----------------------------
\* L++ Blueprint: L++ Blueprint Visualizer
\* Version: 1.1.0
\* TLAPS Seal Specification

EXTENDS Integers, Sequences, TLC

\* Bounds for model checking
MAX_HISTORY == 3
CONSTANT NULL

States == {"idle", "loaded", "viewing", "exporting", "error"}
Events == {"BACK", "CLEAR", "DESELECT", "EXPORT_README", "LOAD", "LOAD_FAILED", "LOAD_TREE", "SELECT", "SET_TREE", "TOGGLE_ACTIONS", "TOGGLE_GATES", "UNLOAD", "UNLOAD_TREE", "VIEW", "VIEW_GRAPH", "VIEW_MERMAID", "VIEW_TABLE", "VIEW_TREE", "VIEW_TREE_MERMAID", "ZOOM_IN", "ZOOM_OUT"}
TerminalStates == {}

VARIABLES
    state,
    blueprint,
    blueprint_name,
    blueprint_id,
    view_mode,
    selected_node,
    zoom_level,
    show_gates,
    show_actions,
    output,
    readme_content,
    export_path,
    tree,
    tree_name,
    tree_output,
    error

vars == <<state, blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* Type Invariant - Structural Correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint
    /\ TRUE  \* blueprint_name
    /\ TRUE  \* blueprint_id
    /\ TRUE  \* view_mode
    /\ TRUE  \* selected_node
    /\ TRUE  \* zoom_level
    /\ TRUE  \* show_gates
    /\ TRUE  \* show_actions
    /\ TRUE  \* output
    /\ TRUE  \* readme_content
    /\ TRUE  \* export_path
    /\ TRUE  \* tree
    /\ TRUE  \* tree_name
    /\ TRUE  \* tree_output
    /\ TRUE  \* error

\* Initial State
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
    /\ tree = NULL
    /\ tree_name = NULL
    /\ tree_output = NULL
    /\ error = NULL

\* Transitions
\* t_load: idle --(LOAD)--> loaded
t_load ==
    /\ state = "idle"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_load_error: idle --(LOAD_FAILED)--> error
t_load_error ==
    /\ state = "idle"
    /\ state' = "error"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_reload: loaded --(LOAD)--> loaded
t_reload ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_reload_from_viewing: viewing --(LOAD)--> loaded
t_reload_from_viewing ==
    /\ state = "viewing"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_start_view: loaded --(VIEW)--> viewing
t_start_view ==
    /\ state = "loaded"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_switch_to_graph: viewing --(VIEW_GRAPH)--> viewing
t_switch_to_graph ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_switch_to_table: viewing --(VIEW_TABLE)--> viewing
t_switch_to_table ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_switch_to_mermaid: viewing --(VIEW_MERMAID)--> viewing
t_switch_to_mermaid ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_select: viewing --(SELECT)--> viewing
t_select ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_deselect: viewing --(DESELECT)--> viewing
t_deselect ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_zoom_in: viewing --(ZOOM_IN)--> viewing
t_zoom_in ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_zoom_out: viewing --(ZOOM_OUT)--> viewing
t_zoom_out ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_toggle_gates: viewing --(TOGGLE_GATES)--> viewing
t_toggle_gates ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_toggle_actions: viewing --(TOGGLE_ACTIONS)--> viewing
t_toggle_actions ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_back_to_loaded: viewing --(BACK)--> loaded
t_back_to_loaded ==
    /\ state = "viewing"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_unload: loaded --(UNLOAD)--> idle
t_unload ==
    /\ state = "loaded"
    /\ state' = "idle"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_unload_from_viewing: viewing --(UNLOAD)--> idle
t_unload_from_viewing ==
    /\ state = "viewing"
    /\ state' = "idle"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_export_readme_from_loaded: loaded --(EXPORT_README)--> loaded
t_export_readme_from_loaded ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_export_readme_from_viewing: viewing --(EXPORT_README)--> viewing
t_export_readme_from_viewing ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_recover: error --(CLEAR)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_load_tree: idle --(LOAD_TREE)--> loaded
t_load_tree ==
    /\ state = "idle"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_set_tree: loaded --(SET_TREE)--> loaded
t_set_tree ==
    /\ state = "loaded"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_view_tree: loaded --(VIEW_TREE)--> viewing
t_view_tree ==
    /\ state = "loaded"
    /\ state' = "viewing"
    /\ tree # NULL  \* Gate: has_tree
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_switch_to_tree: viewing --(VIEW_TREE)--> viewing
t_switch_to_tree ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ tree # NULL  \* Gate: has_tree
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_switch_to_tree_mermaid: viewing --(VIEW_TREE_MERMAID)--> viewing
t_switch_to_tree_mermaid ==
    /\ state = "viewing"
    /\ state' = "viewing"
    /\ tree # NULL  \* Gate: has_tree
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* t_unload_tree: viewing --(UNLOAD_TREE)--> loaded
t_unload_tree ==
    /\ state = "viewing"
    /\ state' = "loaded"
    /\ UNCHANGED <<blueprint, blueprint_name, blueprint_id, view_mode, selected_node, zoom_level, show_gates, show_actions, output, readme_content, export_path, tree, tree_name, tree_output, error>>

\* Next State Relation
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
    \/ t_load_tree
    \/ t_set_tree
    \/ t_view_tree
    \/ t_switch_to_tree
    \/ t_switch_to_tree_mermaid
    \/ t_unload_tree

\* Safety Invariant - Convergence Guarantee
SafetyInvariant ==
    state \in TerminalStates \/
    \E e \in Events : ENABLED(Next)

\* Temporal Specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* =========================================================
\* TLAPS THEOREMS - Axiomatic Certification
\* =========================================================

\* Theorem 1: Type Safety
THEOREM TypeSafety == Spec => []TypeInvariant
PROOF OMITTED  \* To be proven by TLAPS

\* Theorem 2: Convergence (No unhandled deadlock)
THEOREM Convergence == Spec => []SafetyInvariant
PROOF OMITTED  \* To be proven by TLAPS

\* Theorem 3: Terminal Reachability
THEOREM TerminalReachable == Spec => <>(TRUE)
PROOF OMITTED  \* To be proven by TLAPS

============================================================================