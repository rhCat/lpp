---------------------------- MODULE task_orchestrator ----------------------------
\* L++ Blueprint: Hierarchical Task Orchestrator
\* Version: 2.0.0
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
States == {"idle", "analyzing", "expanding", "planning", "building", "executing", "traversing", "reflecting", "evaluating", "complete", "error"}

Events == {"DONE", "RESET", "RETRY", "START", "SUBMIT"}

TerminalStates == {"complete"}

VARIABLES
    state,           \* Current state
    api_key,           \* Context variable
    api_base,           \* Context variable
    model,           \* Context variable
    task,           \* Root task
    feature_tree,           \* Hierarchical tree
    current_path,           \* Path to node
    current_feature,           \* Active feature
    depth,           \* Current depth
    max_depth,           \* Max depth
    is_leaf,           \* Node is atomic
    leaf_queue,           \* Leaves to execute
    leaf_count,           \* Context variable
    exec_count,           \* Executed count
    tools_needed,           \* Context variable
    tools_pending,           \* Context variable
    tools_built,           \* Context variable
    exec_log,           \* Execution log
    reflection,           \* Context variable
    evaluation,           \* Context variable
    is_complete,           \* Context variable
    iteration,           \* Context variable
    max_iterations,           \* Context variable
    workspace_path,           \* Context variable
    error,           \* Context variable
    event_history    \* Trace of events

vars == <<state, api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* api_key: any string or NULL
    /\ TRUE  \* api_base: any string or NULL
    /\ TRUE  \* model: any string or NULL
    /\ TRUE  \* task: any string or NULL
    /\ TRUE  \* feature_tree: any string or NULL
    /\ TRUE  \* current_path: any string or NULL
    /\ TRUE  \* current_feature: any string or NULL
    /\ (depth \in BoundedInt) \/ (depth = NULL)
    /\ (max_depth \in BoundedInt) \/ (max_depth = NULL)
    /\ (is_leaf \in BOOLEAN) \/ (is_leaf = NULL)
    /\ TRUE  \* leaf_queue: any string or NULL
    /\ (leaf_count \in BoundedInt) \/ (leaf_count = NULL)
    /\ (exec_count \in BoundedInt) \/ (exec_count = NULL)
    /\ TRUE  \* tools_needed: any string or NULL
    /\ (tools_pending \in BoundedInt) \/ (tools_pending = NULL)
    /\ TRUE  \* tools_built: any string or NULL
    /\ TRUE  \* exec_log: any string or NULL
    /\ TRUE  \* reflection: any string or NULL
    /\ TRUE  \* evaluation: any string or NULL
    /\ (is_complete \in BOOLEAN) \/ (is_complete = NULL)
    /\ (iteration \in BoundedInt) \/ (iteration = NULL)
    /\ (max_iterations \in BoundedInt) \/ (max_iterations = NULL)
    /\ TRUE  \* workspace_path: any string or NULL
    /\ TRUE  \* error: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (depth = NULL) \/ (depth \in BoundedInt)
    /\ (max_depth = NULL) \/ (max_depth \in BoundedInt)
    /\ (leaf_count = NULL) \/ (leaf_count \in BoundedInt)
    /\ (exec_count = NULL) \/ (exec_count \in BoundedInt)
    /\ (tools_pending = NULL) \/ (tools_pending \in BoundedInt)
    /\ (iteration = NULL) \/ (iteration \in BoundedInt)
    /\ (max_iterations = NULL) \/ (max_iterations \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ api_key = NULL
    /\ api_base = NULL
    /\ model = NULL
    /\ task = NULL
    /\ feature_tree = NULL
    /\ current_path = NULL
    /\ current_feature = NULL
    /\ depth = NULL
    /\ max_depth = NULL
    /\ is_leaf = NULL
    /\ leaf_queue = NULL
    /\ leaf_count = NULL
    /\ exec_count = NULL
    /\ tools_needed = NULL
    /\ tools_pending = NULL
    /\ tools_built = NULL
    /\ exec_log = NULL
    /\ reflection = NULL
    /\ evaluation = NULL
    /\ is_complete = NULL
    /\ iteration = NULL
    /\ max_iterations = NULL
    /\ workspace_path = NULL
    /\ error = NULL
    /\ event_history = <<>>

\* Transitions
\* t_start: idle --(START)--> idle
t_start ==
    /\ state = "idle"
    /\ state' = "idle"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "START")

\* t_submit: idle --(SUBMIT)--> analyzing
t_submit ==
    /\ state = "idle"
    /\ state' = "analyzing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "SUBMIT")

\* t_ana_expand: analyzing --(DONE)--> expanding
t_ana_expand ==
    /\ state = "analyzing"
    /\ feature_tree /= NULL  \* gate: has_tree
    /\ depth < max_depth /\ is_leaf = FALSE  \* gate: can_expand
    /\ error = NULL  \* gate: no_error
    /\ state' = "expanding"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_ana_atomic: analyzing --(DONE)--> planning
t_ana_atomic ==
    /\ state = "analyzing"
    /\ feature_tree /= NULL  \* gate: has_tree
    /\ is_leaf = TRUE \/ depth >= max_depth  \* gate: is_atomic
    /\ error = NULL  \* gate: no_error
    /\ state' = "planning"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_ana_err: analyzing --(DONE)--> error
t_ana_err ==
    /\ state = "analyzing"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_exp_more: expanding --(DONE)--> expanding
t_exp_more ==
    /\ state = "expanding"
    /\ depth < max_depth /\ is_leaf = FALSE  \* gate: can_expand
    /\ error = NULL  \* gate: no_error
    /\ state' = "expanding"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_exp_done: expanding --(DONE)--> planning
t_exp_done ==
    /\ state = "expanding"
    /\ is_leaf = TRUE \/ depth >= max_depth  \* gate: is_atomic
    /\ error = NULL  \* gate: no_error
    /\ state' = "planning"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_exp_err: expanding --(DONE)--> error
t_exp_err ==
    /\ state = "expanding"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_plan_build: planning --(DONE)--> building
t_plan_build ==
    /\ state = "planning"
    /\ tools_pending /= NULL /\ tools_pending > 0  \* gate: needs_tools
    /\ error = NULL  \* gate: no_error
    /\ state' = "building"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_plan_exec: planning --(DONE)--> executing
t_plan_exec ==
    /\ state = "planning"
    /\ tools_pending = NULL \/ tools_pending = 0  \* gate: no_tools
    /\ error = NULL  \* gate: no_error
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_plan_err: planning --(DONE)--> error
t_plan_err ==
    /\ state = "planning"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_bld_more: building --(DONE)--> building
t_bld_more ==
    /\ state = "building"
    /\ tools_pending /= NULL /\ tools_pending > 0  \* gate: needs_tools
    /\ error = NULL  \* gate: no_error
    /\ state' = "building"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_bld_done: building --(DONE)--> executing
t_bld_done ==
    /\ state = "building"
    /\ tools_pending = NULL \/ tools_pending = 0  \* gate: no_tools
    /\ error = NULL  \* gate: no_error
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_bld_err: building --(DONE)--> error
t_bld_err ==
    /\ state = "building"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_exec_next: executing --(DONE)--> traversing
t_exec_next ==
    /\ state = "executing"
    /\ exec_count < leaf_count  \* gate: has_more
    /\ error = NULL  \* gate: no_error
    /\ state' = "traversing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_exec_done: executing --(DONE)--> reflecting
t_exec_done ==
    /\ state = "executing"
    /\ exec_count >= leaf_count  \* gate: all_done
    /\ error = NULL  \* gate: no_error
    /\ state' = "reflecting"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_exec_err: executing --(DONE)--> error
t_exec_err ==
    /\ state = "executing"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_trav_build: traversing --(DONE)--> building
t_trav_build ==
    /\ state = "traversing"
    /\ tools_pending /= NULL /\ tools_pending > 0  \* gate: needs_tools
    /\ error = NULL  \* gate: no_error
    /\ state' = "building"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_trav_exec: traversing --(DONE)--> executing
t_trav_exec ==
    /\ state = "traversing"
    /\ tools_pending = NULL \/ tools_pending = 0  \* gate: no_tools
    /\ error = NULL  \* gate: no_error
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_trav_err: traversing --(DONE)--> error
t_trav_err ==
    /\ state = "traversing"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_refl_ok: reflecting --(DONE)--> evaluating
t_refl_ok ==
    /\ state = "reflecting"
    /\ error = NULL  \* gate: no_error
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_refl_err: reflecting --(DONE)--> error
t_refl_err ==
    /\ state = "reflecting"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_complete: evaluating --(DONE)--> complete
t_eval_complete ==
    /\ state = "evaluating"
    /\ is_complete = TRUE  \* gate: is_complete
    /\ error = NULL  \* gate: no_error
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_continue: evaluating --(DONE)--> expanding
t_eval_continue ==
    /\ state = "evaluating"
    /\ is_complete = NULL \/ is_complete = FALSE  \* gate: not_complete
    /\ iteration < max_iterations  \* gate: within_iter
    /\ error = NULL  \* gate: no_error
    /\ state' = "expanding"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_max: evaluating --(DONE)--> complete
t_eval_max ==
    /\ state = "evaluating"
    /\ iteration >= max_iterations  \* gate: max_iter
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_err: evaluating --(DONE)--> error
t_eval_err ==
    /\ state = "evaluating"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "DONE")

\* t_recover: error --(RETRY)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "RETRY")

\* t_reset: * --(RESET)--> idle
t_reset ==
    /\ TRUE  \* from any state
    /\ state' = "idle"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ task' = task
    /\ feature_tree' = feature_tree
    /\ current_path' = current_path
    /\ current_feature' = current_feature
    /\ depth' = depth
    /\ max_depth' = max_depth
    /\ is_leaf' = is_leaf
    /\ leaf_queue' = leaf_queue
    /\ leaf_count' = leaf_count
    /\ exec_count' = exec_count
    /\ tools_needed' = tools_needed
    /\ tools_pending' = tools_pending
    /\ tools_built' = tools_built
    /\ exec_log' = exec_log
    /\ reflection' = reflection
    /\ evaluation' = evaluation
    /\ is_complete' = is_complete
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ workspace_path' = workspace_path
    /\ error' = error
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t_start
    \/ t_submit
    \/ t_ana_expand
    \/ t_ana_atomic
    \/ t_ana_err
    \/ t_exp_more
    \/ t_exp_done
    \/ t_exp_err
    \/ t_plan_build
    \/ t_plan_exec
    \/ t_plan_err
    \/ t_bld_more
    \/ t_bld_done
    \/ t_bld_err
    \/ t_exec_next
    \/ t_exec_done
    \/ t_exec_err
    \/ t_trav_build
    \/ t_trav_exec
    \/ t_trav_err
    \/ t_refl_ok
    \/ t_refl_err
    \/ t_eval_complete
    \/ t_eval_continue
    \/ t_eval_max
    \/ t_eval_err
    \/ t_recover
    \/ t_reset

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

\* Terminal states are reachable
TerminalReachable == <>(state = "complete")

=============================================================================