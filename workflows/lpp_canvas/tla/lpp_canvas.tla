---------------------------- MODULE lpp_canvas ----------------------------
\* L++ Blueprint: L++ Canvas
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

\* =========================================================
\* DOMAINS - Auto-extracted from context_schema
\* =========================================================
ModeDomain == {"create", "edit", "review", "simulate"}
SelectedTypeDomain == {"state", "transition", "gate", "action"}
ReviewStatusDomain == {"pending", "approved", "rejected"}

\* States
States == {"idle", "loaded", "creating", "editing", "reviewing", "validating", "analyzing", "simulating", "clustering", "llm_assist", "generating", "saving", "error"}

Events == {"ADD_ACTION", "ADD_GATE", "ADD_NOTE", "ADD_STATE", "ADD_TRANSITION", "ANALYZE", "APPLY", "APPROVE", "CANCEL", "CLOSE", "CLUSTER", "CREATE", "DELETE", "DISPATCH", "DONE", "ERROR", "GENERATE", "LLM_ASSIST", "LOAD", "NEW", "QUERY", "REJECT", "RESET", "RETRY", "REVIEW", "SAVE", "SELECT", "SIMULATE", "STEP", "VALIDATE"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    blueprint,           \* Current blueprint being edited
    blueprint_path,           \* Path to blueprint file
    blueprint_json,           \* JSON string of blueprint
    is_dirty,           \* Has unsaved changes
    mode,           \* Context variable
    llm_enabled,           \* LLM assistance enabled
    api_key,           \* Context variable
    api_base,           \* Context variable
    model,           \* Context variable
    prompt,           \* User prompt for LLM
    llm_response,           \* LLM response
    suggestions,           \* LLM suggestions
    selected_node,           \* Currently selected state/transition
    selected_type,           \* Context variable
    node_data,           \* Data for selected node
    edit_buffer,           \* Pending edits
    tlc_result,           \* TLC validation result
    tlc_errors,           \* TLC validation errors
    tlc_passed,           \* Context variable
    paths,           \* All execution paths
    path_count,           \* Context variable
    states_list,           \* All states
    state_count,           \* Context variable
    reachability,           \* State reachability map
    deadlocks,           \* Detected deadlock states
    sim_state,           \* Current simulation state
    sim_context,           \* Simulation context data
    sim_history,           \* Simulation step history
    sim_available_events,           \* Events available at current state
    sim_step_count,           \* Context variable
    clusters,           \* State clusters
    dependencies,           \* State dependency graph
    sorted_states,           \* Topologically sorted states
    audit_log,           \* Audit trail of changes
    review_notes,           \* Review comments
    review_status,           \* Context variable
    coverage,           \* Test coverage metrics
    graph_html,           \* Generated graph HTML
    mermaid,           \* Generated Mermaid diagram
    error,           \* Context variable
    event_history    \* Trace of events

vars == <<state, blueprint, blueprint_path, blueprint_json, is_dirty, mode, llm_enabled, api_key, api_base, model, prompt, llm_response, suggestions, selected_node, selected_type, node_data, edit_buffer, tlc_result, tlc_errors, tlc_passed, paths, path_count, states_list, state_count, reachability, deadlocks, sim_state, sim_context, sim_history, sim_available_events, sim_step_count, clusters, dependencies, sorted_states, audit_log, review_notes, review_status, coverage, graph_html, mermaid, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* blueprint: any string or NULL
    /\ TRUE  \* blueprint_path: any string or NULL
    /\ TRUE  \* blueprint_json: any string or NULL
    /\ (is_dirty \in BOOLEAN) \/ (is_dirty = NULL)
    /\ (mode \in ModeDomain) \/ (mode = NULL)
    /\ (llm_enabled \in BOOLEAN) \/ (llm_enabled = NULL)
    /\ TRUE  \* api_key: any string or NULL
    /\ TRUE  \* api_base: any string or NULL
    /\ TRUE  \* model: any string or NULL
    /\ TRUE  \* prompt: any string or NULL
    /\ TRUE  \* llm_response: any string or NULL
    /\ TRUE  \* suggestions: any string or NULL
    /\ TRUE  \* selected_node: any string or NULL
    /\ (selected_type \in SelectedTypeDomain) \/ (selected_type = NULL)
    /\ TRUE  \* node_data: any string or NULL
    /\ TRUE  \* edit_buffer: any string or NULL
    /\ TRUE  \* tlc_result: any string or NULL
    /\ TRUE  \* tlc_errors: any string or NULL
    /\ (tlc_passed \in BOOLEAN) \/ (tlc_passed = NULL)
    /\ TRUE  \* paths: any string or NULL
    /\ (path_count \in BoundedInt) \/ (path_count = NULL)
    /\ TRUE  \* states_list: any string or NULL
    /\ (state_count \in BoundedInt) \/ (state_count = NULL)
    /\ TRUE  \* reachability: any string or NULL
    /\ TRUE  \* deadlocks: any string or NULL
    /\ TRUE  \* sim_state: any string or NULL
    /\ TRUE  \* sim_context: any string or NULL
    /\ TRUE  \* sim_history: any string or NULL
    /\ TRUE  \* sim_available_events: any string or NULL
    /\ (sim_step_count \in BoundedInt) \/ (sim_step_count = NULL)
    /\ TRUE  \* clusters: any string or NULL
    /\ TRUE  \* dependencies: any string or NULL
    /\ TRUE  \* sorted_states: any string or NULL
    /\ TRUE  \* audit_log: any string or NULL
    /\ TRUE  \* review_notes: any string or NULL
    /\ (review_status \in ReviewStatusDomain) \/ (review_status = NULL)
    /\ TRUE  \* coverage: any string or NULL
    /\ TRUE  \* graph_html: any string or NULL
    /\ TRUE  \* mermaid: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (path_count = NULL) \/ (path_count \in BoundedInt)
    /\ (state_count = NULL) \/ (state_count \in BoundedInt)
    /\ (sim_step_count = NULL) \/ (sim_step_count \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ blueprint = NULL
    /\ blueprint_path = NULL
    /\ blueprint_json = NULL
    /\ is_dirty = NULL
    /\ mode = NULL
    /\ llm_enabled = NULL
    /\ api_key = NULL
    /\ api_base = NULL
    /\ model = NULL
    /\ prompt = NULL
    /\ llm_response = NULL
    /\ suggestions = NULL
    /\ selected_node = NULL
    /\ selected_type = NULL
    /\ node_data = NULL
    /\ edit_buffer = NULL
    /\ tlc_result = NULL
    /\ tlc_errors = NULL
    /\ tlc_passed = NULL
    /\ paths = NULL
    /\ path_count = NULL
    /\ states_list = NULL
    /\ state_count = NULL
    /\ reachability = NULL
    /\ deadlocks = NULL
    /\ sim_state = NULL
    /\ sim_context = NULL
    /\ sim_history = NULL
    /\ sim_available_events = NULL
    /\ sim_step_count = NULL
    /\ clusters = NULL
    /\ dependencies = NULL
    /\ sorted_states = NULL
    /\ audit_log = NULL
    /\ review_notes = NULL
    /\ review_status = NULL
    /\ coverage = NULL
    /\ graph_html = NULL
    /\ mermaid = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_new: idle --(NEW)--> creating
t_new ==
    /\ state = "idle"
    /\ state' = "creating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "NEW")

\* t_load: idle --(LOAD)--> loaded
t_load ==
    /\ state = "idle"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_load_err: idle --(LOAD)--> error
t_load_err ==
    /\ state = "idle"
    /\ error /= None  \* gate: g_load_failed
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "LOAD")

\* t_create_done: creating --(CREATE)--> loaded
t_create_done ==
    /\ state = "creating"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "CREATE")

\* t_create_llm: creating --(LLM_ASSIST)--> llm_assist
t_create_llm ==
    /\ state = "creating"
    /\ llm_enabled = TRUE /\ api_key /= None  \* gate: g_llm_enabled
    /\ state' = "llm_assist"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "LLM_ASSIST")

\* t_create_cancel: creating --(CANCEL)--> idle
t_create_cancel ==
    /\ state = "creating"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "CANCEL")

\* t_select: loaded --(SELECT)--> editing
t_select ==
    /\ state = "loaded"
    /\ selected_node /= None  \* gate: g_has_selection
    /\ state' = "editing"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "SELECT")

\* t_review: loaded --(REVIEW)--> reviewing
t_review ==
    /\ state = "loaded"
    /\ state' = "reviewing"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "REVIEW")

\* t_validate: loaded --(VALIDATE)--> validating
t_validate ==
    /\ state = "loaded"
    /\ state' = "validating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "VALIDATE")

\* t_analyze: loaded --(ANALYZE)--> analyzing
t_analyze ==
    /\ state = "loaded"
    /\ state' = "analyzing"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ANALYZE")

\* t_simulate: loaded --(SIMULATE)--> simulating
t_simulate ==
    /\ state = "loaded"
    /\ state' = "simulating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "SIMULATE")

\* t_cluster: loaded --(CLUSTER)--> clustering
t_cluster ==
    /\ state = "loaded"
    /\ state' = "clustering"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "CLUSTER")

\* t_generate: loaded --(GENERATE)--> generating
t_generate ==
    /\ state = "loaded"
    /\ state' = "generating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE")

\* t_llm_loaded: loaded --(LLM_ASSIST)--> llm_assist
t_llm_loaded ==
    /\ state = "loaded"
    /\ llm_enabled = TRUE /\ api_key /= None  \* gate: g_llm_enabled
    /\ state' = "llm_assist"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "LLM_ASSIST")

\* t_save: loaded --(SAVE)--> saving
t_save ==
    /\ state = "loaded"
    /\ is_dirty = TRUE  \* gate: g_is_dirty
    /\ state' = "saving"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "SAVE")

\* t_close: loaded --(CLOSE)--> idle
t_close ==
    /\ state = "loaded"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "CLOSE")

\* t_edit_apply: editing --(APPLY)--> loaded
t_edit_apply ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "APPLY")

\* t_edit_cancel: editing --(CANCEL)--> loaded
t_edit_cancel ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "CANCEL")

\* t_edit_llm: editing --(LLM_ASSIST)--> llm_assist
t_edit_llm ==
    /\ state = "editing"
    /\ llm_enabled = TRUE /\ api_key /= None  \* gate: g_llm_enabled
    /\ state' = "llm_assist"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "LLM_ASSIST")

\* t_edit_delete: editing --(DELETE)--> loaded
t_edit_delete ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DELETE")

\* t_add_state: editing --(ADD_STATE)--> loaded
t_add_state ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ADD_STATE")

\* t_add_trans: editing --(ADD_TRANSITION)--> loaded
t_add_trans ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ADD_TRANSITION")

\* t_add_gate: editing --(ADD_GATE)--> loaded
t_add_gate ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ADD_GATE")

\* t_add_action: editing --(ADD_ACTION)--> loaded
t_add_action ==
    /\ state = "editing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ADD_ACTION")

\* t_review_note: reviewing --(ADD_NOTE)--> reviewing
t_review_note ==
    /\ state = "reviewing"
    /\ prompt /= None  \* gate: g_has_prompt
    /\ state' = "reviewing"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ADD_NOTE")

\* t_review_approve: reviewing --(APPROVE)--> loaded
t_review_approve ==
    /\ state = "reviewing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "APPROVE")

\* t_review_reject: reviewing --(REJECT)--> loaded
t_review_reject ==
    /\ state = "reviewing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "REJECT")

\* t_review_done: reviewing --(DONE)--> loaded
t_review_done ==
    /\ state = "reviewing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_done: validating --(DONE)--> loaded
t_validate_done ==
    /\ state = "validating"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_to_gen: validating --(GENERATE)--> generating
t_validate_to_gen ==
    /\ state = "validating"
    /\ tlc_passed = TRUE  \* gate: g_tlc_passed
    /\ state' = "generating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "GENERATE")

\* t_validate_err: validating --(ERROR)--> error
t_validate_err ==
    /\ state = "validating"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t_analyze_done: analyzing --(DONE)--> loaded
t_analyze_done ==
    /\ state = "analyzing"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_sim_step: simulating --(STEP)--> simulating
t_sim_step ==
    /\ state = "simulating"
    /\ simstate /= None  \* gate: g_sim_not_terminal
    /\ sim_step_count < 1000  \* gate: g_sim_step_limit
    /\ sim_available_events /= None  \* gate: g_has_available_events
    /\ state' = "simulating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "STEP")

\* t_sim_event: simulating --(DISPATCH)--> simulating
t_sim_event ==
    /\ state = "simulating"
    /\ simstate /= None  \* gate: g_sim_not_terminal
    /\ sim_step_count < 1000  \* gate: g_sim_step_limit
    /\ state' = "simulating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DISPATCH")

\* t_sim_reset: simulating --(RESET)--> simulating
t_sim_reset ==
    /\ state = "simulating"
    /\ blueprint /= None  \* gate: g_has_blueprint
    /\ state' = "simulating"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* t_sim_done: simulating --(DONE)--> loaded
t_sim_done ==
    /\ state = "simulating"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_cluster_done: clustering --(DONE)--> loaded
t_cluster_done ==
    /\ state = "clustering"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_llm_done: llm_assist --(DONE)--> loaded
t_llm_done ==
    /\ state = "llm_assist"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_llm_apply: llm_assist --(APPLY)--> loaded
t_llm_apply ==
    /\ state = "llm_assist"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "APPLY")

\* t_llm_cancel: llm_assist --(CANCEL)--> loaded
t_llm_cancel ==
    /\ state = "llm_assist"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "CANCEL")

\* t_llm_query: llm_assist --(QUERY)--> llm_assist
t_llm_query ==
    /\ state = "llm_assist"
    /\ prompt /= None  \* gate: g_has_prompt
    /\ llm_enabled = TRUE /\ api_key /= None  \* gate: g_llm_enabled
    /\ state' = "llm_assist"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "QUERY")

\* t_generate_done: generating --(DONE)--> loaded
t_generate_done ==
    /\ state = "generating"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_save_done: saving --(DONE)--> loaded
t_save_done ==
    /\ state = "saving"
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_save_err: saving --(ERROR)--> error
t_save_err ==
    /\ state = "saving"
    /\ state' = "error"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "ERROR")

\* t_err_retry: error --(RETRY)--> loaded
t_err_retry ==
    /\ state = "error"
    /\ blueprint /= None  \* gate: g_has_blueprint
    /\ state' = "loaded"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "RETRY")

\* t_err_reset: error --(RESET)--> idle
t_err_reset ==
    /\ state = "error"
    /\ state' = "idle"
    /\ blueprint' = blueprint
    /\ blueprint_path' = blueprint_path
    /\ blueprint_json' = blueprint_json
    /\ is_dirty' = is_dirty
    /\ mode' = mode
    /\ llm_enabled' = llm_enabled
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ prompt' = prompt
    /\ llm_response' = llm_response
    /\ suggestions' = suggestions
    /\ selected_node' = selected_node
    /\ selected_type' = selected_type
    /\ node_data' = node_data
    /\ edit_buffer' = edit_buffer
    /\ tlc_result' = tlc_result
    /\ tlc_errors' = tlc_errors
    /\ tlc_passed' = tlc_passed
    /\ paths' = paths
    /\ path_count' = path_count
    /\ states_list' = states_list
    /\ state_count' = state_count
    /\ reachability' = reachability
    /\ deadlocks' = deadlocks
    /\ sim_state' = sim_state
    /\ sim_context' = sim_context
    /\ sim_history' = sim_history
    /\ sim_available_events' = sim_available_events
    /\ sim_step_count' = sim_step_count
    /\ clusters' = clusters
    /\ dependencies' = dependencies
    /\ sorted_states' = sorted_states
    /\ audit_log' = audit_log
    /\ review_notes' = review_notes
    /\ review_status' = review_status
    /\ coverage' = coverage
    /\ graph_html' = graph_html
    /\ mermaid' = mermaid
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t_new
    \/ t_load
    \/ t_load_err
    \/ t_create_done
    \/ t_create_llm
    \/ t_create_cancel
    \/ t_select
    \/ t_review
    \/ t_validate
    \/ t_analyze
    \/ t_simulate
    \/ t_cluster
    \/ t_generate
    \/ t_llm_loaded
    \/ t_save
    \/ t_close
    \/ t_edit_apply
    \/ t_edit_cancel
    \/ t_edit_llm
    \/ t_edit_delete
    \/ t_add_state
    \/ t_add_trans
    \/ t_add_gate
    \/ t_add_action
    \/ t_review_note
    \/ t_review_approve
    \/ t_review_reject
    \/ t_review_done
    \/ t_validate_done
    \/ t_validate_to_gen
    \/ t_validate_err
    \/ t_analyze_done
    \/ t_sim_step
    \/ t_sim_event
    \/ t_sim_reset
    \/ t_sim_done
    \/ t_cluster_done
    \/ t_llm_done
    \/ t_llm_apply
    \/ t_llm_cancel
    \/ t_llm_query
    \/ t_generate_done
    \/ t_save_done
    \/ t_save_err
    \/ t_err_retry
    \/ t_err_reset

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================