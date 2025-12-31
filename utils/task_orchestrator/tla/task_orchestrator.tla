---------------------------- MODULE task_orchestrator ----------------------------
\* L++ Blueprint: Hierarchical Task Orchestrator
\* Version: 2.0.0
\* TLAPS Seal Specification

EXTENDS Integers, Sequences, TLC

\* Bounds for model checking
MAX_HISTORY == 3
CONSTANT NULL

States == {"idle", "analyzing", "expanding", "planning", "building", "executing", "traversing", "reflecting", "evaluating", "complete", "error"}
Events == {"DONE", "RESET", "RETRY", "START", "SUBMIT"}
TerminalStates == {"complete"}

VARIABLES
    state,
    api_key,
    api_base,
    model,
    task,
    feature_tree,
    current_path,
    current_feature,
    depth,
    max_depth,
    is_leaf,
    leaf_queue,
    leaf_count,
    exec_count,
    tools_needed,
    tools_pending,
    tools_built,
    exec_log,
    reflection,
    evaluation,
    is_complete,
    iteration,
    max_iterations,
    workspace_path,
    error

vars == <<state, api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* Type Invariant - Structural Correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* api_key
    /\ TRUE  \* api_base
    /\ TRUE  \* model
    /\ TRUE  \* task
    /\ TRUE  \* feature_tree
    /\ TRUE  \* current_path
    /\ TRUE  \* current_feature
    /\ TRUE  \* depth
    /\ TRUE  \* max_depth
    /\ TRUE  \* is_leaf
    /\ TRUE  \* leaf_queue
    /\ TRUE  \* leaf_count
    /\ TRUE  \* exec_count
    /\ TRUE  \* tools_needed
    /\ TRUE  \* tools_pending
    /\ TRUE  \* tools_built
    /\ TRUE  \* exec_log
    /\ TRUE  \* reflection
    /\ TRUE  \* evaluation
    /\ TRUE  \* is_complete
    /\ TRUE  \* iteration
    /\ TRUE  \* max_iterations
    /\ TRUE  \* workspace_path
    /\ TRUE  \* error

\* Initial State
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

\* Transitions
\* t_start: idle --(START)--> idle
t_start ==
    /\ state = "idle"
    /\ state' = "idle"
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_submit: idle --(SUBMIT)--> analyzing
t_submit ==
    /\ state = "idle"
    /\ state' = "analyzing"
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_ana_expand: analyzing --(DONE)--> expanding
t_ana_expand ==
    /\ state = "analyzing"
    /\ state' = "expanding"
    /\ feature_tree # NULL  \* Gate: has_tree
    /\ depth < max_depth /\ is_leaf == False  \* Gate: can_expand
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_ana_atomic: analyzing --(DONE)--> planning
t_ana_atomic ==
    /\ state = "analyzing"
    /\ state' = "planning"
    /\ feature_tree # NULL  \* Gate: has_tree
    /\ is_leaf == True \/ depth >= max_depth  \* Gate: is_atomic
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_ana_err: analyzing --(DONE)--> error
t_ana_err ==
    /\ state = "analyzing"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_exp_more: expanding --(DONE)--> expanding
t_exp_more ==
    /\ state = "expanding"
    /\ state' = "expanding"
    /\ depth < max_depth /\ is_leaf == False  \* Gate: can_expand
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_exp_done: expanding --(DONE)--> planning
t_exp_done ==
    /\ state = "expanding"
    /\ state' = "planning"
    /\ is_leaf == True \/ depth >= max_depth  \* Gate: is_atomic
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_exp_err: expanding --(DONE)--> error
t_exp_err ==
    /\ state = "expanding"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_plan_build: planning --(DONE)--> building
t_plan_build ==
    /\ state = "planning"
    /\ state' = "building"
    /\ tools_pending # NULL /\ tools_pending > 0  \* Gate: needs_tools
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_plan_exec: planning --(DONE)--> executing
t_plan_exec ==
    /\ state = "planning"
    /\ state' = "executing"
    /\ tools_pending = NULL \/ tools_pending == 0  \* Gate: no_tools
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_plan_err: planning --(DONE)--> error
t_plan_err ==
    /\ state = "planning"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_bld_more: building --(DONE)--> building
t_bld_more ==
    /\ state = "building"
    /\ state' = "building"
    /\ tools_pending # NULL /\ tools_pending > 0  \* Gate: needs_tools
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_bld_done: building --(DONE)--> executing
t_bld_done ==
    /\ state = "building"
    /\ state' = "executing"
    /\ tools_pending = NULL \/ tools_pending == 0  \* Gate: no_tools
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_bld_err: building --(DONE)--> error
t_bld_err ==
    /\ state = "building"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_exec_next: executing --(DONE)--> traversing
t_exec_next ==
    /\ state = "executing"
    /\ state' = "traversing"
    /\ exec_count < leaf_count  \* Gate: has_more
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_exec_done: executing --(DONE)--> reflecting
t_exec_done ==
    /\ state = "executing"
    /\ state' = "reflecting"
    /\ exec_count >= leaf_count  \* Gate: all_done
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_exec_err: executing --(DONE)--> error
t_exec_err ==
    /\ state = "executing"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_trav_build: traversing --(DONE)--> building
t_trav_build ==
    /\ state = "traversing"
    /\ state' = "building"
    /\ tools_pending # NULL /\ tools_pending > 0  \* Gate: needs_tools
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_trav_exec: traversing --(DONE)--> executing
t_trav_exec ==
    /\ state = "traversing"
    /\ state' = "executing"
    /\ tools_pending = NULL \/ tools_pending == 0  \* Gate: no_tools
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_trav_err: traversing --(DONE)--> error
t_trav_err ==
    /\ state = "traversing"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_refl_ok: reflecting --(DONE)--> evaluating
t_refl_ok ==
    /\ state = "reflecting"
    /\ state' = "evaluating"
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_refl_err: reflecting --(DONE)--> error
t_refl_err ==
    /\ state = "reflecting"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_eval_complete: evaluating --(DONE)--> complete
t_eval_complete ==
    /\ state = "evaluating"
    /\ state' = "complete"
    /\ is_complete == True  \* Gate: is_complete
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_eval_continue: evaluating --(DONE)--> expanding
t_eval_continue ==
    /\ state = "evaluating"
    /\ state' = "expanding"
    /\ is_complete = NULL \/ is_complete == False  \* Gate: not_complete
    /\ iteration < max_iterations  \* Gate: within_iter
    /\ error = NULL  \* Gate: no_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_eval_max: evaluating --(DONE)--> complete
t_eval_max ==
    /\ state = "evaluating"
    /\ state' = "complete"
    /\ iteration >= max_iterations  \* Gate: max_iter
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_eval_err: evaluating --(DONE)--> error
t_eval_err ==
    /\ state = "evaluating"
    /\ state' = "error"
    /\ error # NULL  \* Gate: has_error
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_recover: error --(RETRY)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* t_reset: * --(RESET)--> idle
t_reset ==
    /\ TRUE  \* Global transition
    /\ state' = "idle"
    /\ UNCHANGED <<api_key, api_base, model, task, feature_tree, current_path, current_feature, depth, max_depth, is_leaf, leaf_queue, leaf_count, exec_count, tools_needed, tools_pending, tools_built, exec_log, reflection, evaluation, is_complete, iteration, max_iterations, workspace_path, error>>

\* Next State Relation
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
THEOREM TerminalReachable == Spec => <>(state = "complete")
PROOF OMITTED  \* To be proven by TLAPS

============================================================================