---------------------------- MODULE skill_contractor ----------------------------
\* L++ Blueprint: Skill Contractor
\* Version: 1.7.0
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
States == {"idle", "planning", "executing", "parsing", "correcting", "stepping", "validating", "eval_interactive", "evaluating", "refining", "reviewing", "complete", "error"}

Events == {"DONE", "RESET", "RETRY", "START", "SUBMIT"}

TerminalStates == {"complete"}

VARIABLES
    state,           \* Current state
    api_key,           \* LLM API key
    api_base,           \* LLM API base URL
    model,           \* LLM model identifier
    target,           \* Coding target to achieve
    workspace_path,           \* Working directory
    run_id,           \* Unique identifier for this run (timestamp)
    run_dir,           \* Path to run-specific folder for state and logs
    phase,           \* Current workflow phase: blueprint or implementation
    blueprint_validated,           \* True if blueprint phase passed validation
    plan,           \* Decomposed execution plan
    current_step,           \* Active step being executed
    step_index,           \* Current step index
    step_count,           \* Total steps in plan
    execution_log,           \* History of executed steps
    artifacts,           \* Generated files and outputs
    evaluation,           \* Self-evaluation result
    score,           \* Evaluation score 0-100
    threshold,           \* Score threshold for completion
    feedback,           \* Evaluation feedback
    iteration,           \* Current iteration count
    max_iterations,           \* Max iterations allowed
    is_satisfied,           \* Target achieved flag
    error,           \* Error message if any
    error_count,           \* Consecutive error count
    max_errors,           \* Max errors per step before skip
    last_error,           \* Most recent error for feedback
    step_error_count,           \* Errors on current step
    failed_steps,           \* Steps skipped due to errors
    review_decision,           \* Review outcome: skip or replan
    is_lpp_target,           \* True if target involves L++ skill creation
    lpp_validated,           \* True if L++ artifacts passed validation
    lpp_root,           \* Root path of L++ framework installation
    raw_output,           \* Raw LLM output before parsing
    parsed_output,           \* Parsed and sanitized output
    parse_error,           \* Parse/validation error if any
    corrections,           \* Auto-corrections applied during sanitization (for review)
    corrections_approved,           \* True if corrections were reviewed and approved
    repair_attempts,           \* Number of output repair attempts
    max_repairs,           \* Max repair attempts before re-prompting
    interactive_valid,           \* True if interactive.py passed syntax/import validation
    interactive_feedback,           \* Feedback from interactive evaluation
    event_history    \* Trace of events

vars == <<state, api_key, api_base, model, target, workspace_path, run_id, run_dir, phase, blueprint_validated, plan, current_step, step_index, step_count, execution_log, artifacts, evaluation, score, threshold, feedback, iteration, max_iterations, is_satisfied, error, error_count, max_errors, last_error, step_error_count, failed_steps, review_decision, is_lpp_target, lpp_validated, lpp_root, raw_output, parsed_output, parse_error, corrections, corrections_approved, repair_attempts, max_repairs, interactive_valid, interactive_feedback, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* api_key: any string or NULL
    /\ TRUE  \* api_base: any string or NULL
    /\ TRUE  \* model: any string or NULL
    /\ TRUE  \* target: any string or NULL
    /\ TRUE  \* workspace_path: any string or NULL
    /\ TRUE  \* run_id: any string or NULL
    /\ TRUE  \* run_dir: any string or NULL
    /\ TRUE  \* phase: any string or NULL
    /\ (blueprint_validated \in BOOLEAN) \/ (blueprint_validated = NULL)
    /\ TRUE  \* plan: any string or NULL
    /\ TRUE  \* current_step: any string or NULL
    /\ (step_index \in BoundedInt) \/ (step_index = NULL)
    /\ (step_count \in BoundedInt) \/ (step_count = NULL)
    /\ TRUE  \* execution_log: any string or NULL
    /\ TRUE  \* artifacts: any string or NULL
    /\ TRUE  \* evaluation: any string or NULL
    /\ (score \in BoundedInt) \/ (score = NULL)
    /\ (threshold \in BoundedInt) \/ (threshold = NULL)
    /\ TRUE  \* feedback: any string or NULL
    /\ (iteration \in BoundedInt) \/ (iteration = NULL)
    /\ (max_iterations \in BoundedInt) \/ (max_iterations = NULL)
    /\ (is_satisfied \in BOOLEAN) \/ (is_satisfied = NULL)
    /\ TRUE  \* error: any string or NULL
    /\ (error_count \in BoundedInt) \/ (error_count = NULL)
    /\ (max_errors \in BoundedInt) \/ (max_errors = NULL)
    /\ TRUE  \* last_error: any string or NULL
    /\ (step_error_count \in BoundedInt) \/ (step_error_count = NULL)
    /\ TRUE  \* failed_steps: any string or NULL
    /\ TRUE  \* review_decision: any string or NULL
    /\ (is_lpp_target \in BOOLEAN) \/ (is_lpp_target = NULL)
    /\ (lpp_validated \in BOOLEAN) \/ (lpp_validated = NULL)
    /\ TRUE  \* lpp_root: any string or NULL
    /\ TRUE  \* raw_output: any string or NULL
    /\ TRUE  \* parsed_output: any string or NULL
    /\ TRUE  \* parse_error: any string or NULL
    /\ TRUE  \* corrections: any string or NULL
    /\ (corrections_approved \in BOOLEAN) \/ (corrections_approved = NULL)
    /\ (repair_attempts \in BoundedInt) \/ (repair_attempts = NULL)
    /\ (max_repairs \in BoundedInt) \/ (max_repairs = NULL)
    /\ (interactive_valid \in BOOLEAN) \/ (interactive_valid = NULL)
    /\ TRUE  \* interactive_feedback: any string or NULL

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (step_index = NULL) \/ (step_index \in BoundedInt)
    /\ (step_count = NULL) \/ (step_count \in BoundedInt)
    /\ (score = NULL) \/ (score \in BoundedInt)
    /\ (threshold = NULL) \/ (threshold \in BoundedInt)
    /\ (iteration = NULL) \/ (iteration \in BoundedInt)
    /\ (max_iterations = NULL) \/ (max_iterations \in BoundedInt)
    /\ (error_count = NULL) \/ (error_count \in BoundedInt)
    /\ (max_errors = NULL) \/ (max_errors \in BoundedInt)
    /\ (step_error_count = NULL) \/ (step_error_count \in BoundedInt)
    /\ (repair_attempts = NULL) \/ (repair_attempts \in BoundedInt)
    /\ (max_repairs = NULL) \/ (max_repairs \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ api_key = NULL
    /\ api_base = NULL
    /\ model = NULL
    /\ target = NULL
    /\ workspace_path = NULL
    /\ run_id = NULL
    /\ run_dir = NULL
    /\ phase = NULL
    /\ blueprint_validated = NULL
    /\ plan = NULL
    /\ current_step = NULL
    /\ step_index = NULL
    /\ step_count = NULL
    /\ execution_log = NULL
    /\ artifacts = NULL
    /\ evaluation = NULL
    /\ score = NULL
    /\ threshold = NULL
    /\ feedback = NULL
    /\ iteration = NULL
    /\ max_iterations = NULL
    /\ is_satisfied = NULL
    /\ error = NULL
    /\ error_count = NULL
    /\ max_errors = NULL
    /\ last_error = NULL
    /\ step_error_count = NULL
    /\ failed_steps = NULL
    /\ review_decision = NULL
    /\ is_lpp_target = NULL
    /\ lpp_validated = NULL
    /\ lpp_root = NULL
    /\ raw_output = NULL
    /\ parsed_output = NULL
    /\ parse_error = NULL
    /\ corrections = NULL
    /\ corrections_approved = NULL
    /\ repair_attempts = NULL
    /\ max_repairs = NULL
    /\ interactive_valid = NULL
    /\ interactive_feedback = NULL
    /\ event_history = <<>>

\* Transitions
\* t_start: idle --(START)--> idle
t_start ==
    /\ state = "idle"
    /\ state' = "idle"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "START")

\* t_submit_target: idle --(SUBMIT)--> planning
t_submit_target ==
    /\ state = "idle"
    /\ state' = "planning"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "SUBMIT")

\* t_plan_ready: planning --(DONE)--> executing
t_plan_ready ==
    /\ state = "planning"
    /\ plan /= NULL  \* gate: has_plan
    /\ error = NULL  \* gate: no_error
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_plan_error: planning --(DONE)--> error
t_plan_error ==
    /\ state = "planning"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_exec_to_parse: executing --(DONE)--> parsing
t_exec_to_parse ==
    /\ state = "executing"
    /\ raw_output /= NULL /\ Len(raw_output) > 0  \* gate: has_raw_output
    /\ error = NULL  \* gate: no_error
    /\ state' = "parsing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_exec_error: executing --(DONE)--> error
t_exec_error ==
    /\ state = "executing"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_correct_step: parsing --(DONE)--> correcting
t_parse_ok_correct_step ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections /= NULL /\ Len(corrections) > 0  \* gate: has_corrections
    /\ step_index + 1 < step_count  \* gate: has_more_steps
    /\ state' = "correcting"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_step: parsing --(DONE)--> stepping
t_parse_ok_step ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections = NULL \/ Len(corrections) = 0  \* gate: no_corrections
    /\ step_index + 1 < step_count  \* gate: has_more_steps
    /\ state' = "stepping"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_correct_blueprint_validate: parsing --(DONE)--> correcting
t_parse_ok_correct_blueprint_validate ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections /= NULL /\ Len(corrections) > 0  \* gate: has_corrections
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "blueprint"  \* gate: in_blueprint_phase
    /\ state' = "correcting"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_blueprint_validate: parsing --(DONE)--> validating
t_parse_ok_blueprint_validate ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections = NULL \/ Len(corrections) = 0  \* gate: no_corrections
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "blueprint"  \* gate: in_blueprint_phase
    /\ state' = "validating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_correct_impl_validate: parsing --(DONE)--> correcting
t_parse_ok_correct_impl_validate ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections /= NULL /\ Len(corrections) > 0  \* gate: has_corrections
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "implementation"  \* gate: in_implementation_phase
    /\ state' = "correcting"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_impl_validate: parsing --(DONE)--> validating
t_parse_ok_impl_validate ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections = NULL \/ Len(corrections) = 0  \* gate: no_corrections
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "implementation"  \* gate: in_implementation_phase
    /\ state' = "validating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_correct_eval: parsing --(DONE)--> correcting
t_parse_ok_correct_eval ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections /= NULL /\ Len(corrections) > 0  \* gate: has_corrections
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target /= TRUE  \* gate: not_lpp_target
    /\ state' = "correcting"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_ok_eval: parsing --(DONE)--> evaluating
t_parse_ok_eval ==
    /\ state = "parsing"
    /\ parsed_output /= NULL /\ parse_error = NULL  \* gate: output_valid
    /\ corrections = NULL \/ Len(corrections) = 0  \* gate: no_corrections
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target /= TRUE  \* gate: not_lpp_target
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_correct_to_step: correcting --(DONE)--> stepping
t_correct_to_step ==
    /\ state = "correcting"
    /\ corrections_approved = TRUE  \* gate: corrections_approved
    /\ step_index + 1 < step_count  \* gate: has_more_steps
    /\ state' = "stepping"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_correct_to_validate_blueprint: correcting --(DONE)--> validating
t_correct_to_validate_blueprint ==
    /\ state = "correcting"
    /\ corrections_approved = TRUE  \* gate: corrections_approved
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "blueprint"  \* gate: in_blueprint_phase
    /\ state' = "validating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_correct_to_validate_impl: correcting --(DONE)--> validating
t_correct_to_validate_impl ==
    /\ state = "correcting"
    /\ corrections_approved = TRUE  \* gate: corrections_approved
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "implementation"  \* gate: in_implementation_phase
    /\ state' = "validating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_correct_to_eval: correcting --(DONE)--> evaluating
t_correct_to_eval ==
    /\ state = "correcting"
    /\ corrections_approved = TRUE  \* gate: corrections_approved
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ is_lpp_target /= TRUE  \* gate: not_lpp_target
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_fail_retry: parsing --(DONE)--> executing
t_parse_fail_retry ==
    /\ state = "parsing"
    /\ parse_error /= NULL  \* gate: output_invalid
    /\ (repair_attempts = NULL \/ repair_attempts < max_repairs)  \* gate: can_repair
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_parse_fail_max: parsing --(DONE)--> error
t_parse_fail_max ==
    /\ state = "parsing"
    /\ parse_error /= NULL  \* gate: output_invalid
    /\ (repair_attempts /= NULL /\ repair_attempts >= max_repairs)  \* gate: max_repairs_reached
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_step_exec: stepping --(DONE)--> executing
t_step_exec ==
    /\ state = "stepping"
    /\ step_index + 1 < step_count  \* gate: has_more_steps
    /\ error = NULL  \* gate: no_error
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_step_validate_blueprint: stepping --(DONE)--> validating
t_step_validate_blueprint ==
    /\ state = "stepping"
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ error = NULL  \* gate: no_error
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "blueprint"  \* gate: in_blueprint_phase
    /\ state' = "validating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_step_validate_impl: stepping --(DONE)--> validating
t_step_validate_impl ==
    /\ state = "stepping"
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ error = NULL  \* gate: no_error
    /\ is_lpp_target = TRUE  \* gate: is_lpp_target
    /\ phase = "implementation"  \* gate: in_implementation_phase
    /\ state' = "validating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_step_eval: stepping --(DONE)--> evaluating
t_step_eval ==
    /\ state = "stepping"
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ error = NULL  \* gate: no_error
    /\ is_lpp_target /= TRUE  \* gate: not_lpp_target
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_step_error: stepping --(DONE)--> error
t_step_error ==
    /\ state = "stepping"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_blueprint_pass: validating --(DONE)--> planning
t_validate_blueprint_pass ==
    /\ state = "validating"
    /\ blueprint_validated = TRUE  \* gate: blueprint_validated
    /\ error = NULL  \* gate: no_error
    /\ phase = "blueprint"  \* gate: in_blueprint_phase
    /\ state' = "planning"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_impl_pass: validating --(DONE)--> eval_interactive
t_validate_impl_pass ==
    /\ state = "validating"
    /\ lpp_validated = TRUE  \* gate: lpp_valid
    /\ error = NULL  \* gate: no_error
    /\ phase = "implementation"  \* gate: in_implementation_phase
    /\ state' = "eval_interactive"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_interactive_pass: eval_interactive --(DONE)--> evaluating
t_eval_interactive_pass ==
    /\ state = "eval_interactive"
    /\ interactive_valid = TRUE  \* gate: interactive_valid
    /\ error = NULL  \* gate: no_error
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_interactive_fail: eval_interactive --(DONE)--> refining
t_eval_interactive_fail ==
    /\ state = "eval_interactive"
    /\ interactive_valid /= TRUE  \* gate: interactive_invalid
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_interactive_maxiter: eval_interactive --(DONE)--> evaluating
t_eval_interactive_maxiter ==
    /\ state = "eval_interactive"
    /\ interactive_valid /= TRUE  \* gate: interactive_invalid
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_interactive_error: eval_interactive --(DONE)--> error
t_eval_interactive_error ==
    /\ state = "eval_interactive"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_blueprint_fail: validating --(DONE)--> refining
t_validate_blueprint_fail ==
    /\ state = "validating"
    /\ blueprint_validated /= TRUE  \* gate: blueprint_not_validated
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ phase = "blueprint"  \* gate: in_blueprint_phase
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_impl_fail: validating --(DONE)--> refining
t_validate_impl_fail ==
    /\ state = "validating"
    /\ is_lpp_target = TRUE /\ lpp_validated /= TRUE  \* gate: lpp_invalid
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ phase = "implementation"  \* gate: in_implementation_phase
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_fail_maxiter: validating --(DONE)--> evaluating
t_validate_fail_maxiter ==
    /\ state = "validating"
    /\ is_lpp_target = TRUE /\ lpp_validated /= TRUE  \* gate: lpp_invalid
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_validate_error: validating --(DONE)--> error
t_validate_error ==
    /\ state = "validating"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_satisfied: evaluating --(DONE)--> complete
t_eval_satisfied ==
    /\ state = "evaluating"
    /\ is_satisfied = TRUE  \* gate: is_satisfied
    /\ is_lpp_target /= TRUE \/ lpp_validated = TRUE  \* gate: lpp_ok
    /\ error = NULL  \* gate: no_error
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_lpp_fail: evaluating --(DONE)--> refining
t_eval_lpp_fail ==
    /\ state = "evaluating"
    /\ is_satisfied = TRUE  \* gate: is_satisfied
    /\ is_lpp_target = TRUE /\ lpp_validated /= TRUE  \* gate: lpp_invalid
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ error = NULL  \* gate: no_error
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_refine: evaluating --(DONE)--> refining
t_eval_refine ==
    /\ state = "evaluating"
    /\ is_satisfied = FALSE \/ is_satisfied = NULL  \* gate: not_satisfied
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ error = NULL  \* gate: no_error
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_maxiter: evaluating --(DONE)--> complete
t_eval_maxiter ==
    /\ state = "evaluating"
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ is_lpp_target /= TRUE \/ lpp_validated = TRUE  \* gate: lpp_ok
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_lpp_hard_fail: evaluating --(DONE)--> error
t_eval_lpp_hard_fail ==
    /\ state = "evaluating"
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ is_lpp_target = TRUE /\ lpp_validated /= TRUE  \* gate: lpp_invalid
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_eval_error: evaluating --(DONE)--> error
t_eval_error ==
    /\ state = "evaluating"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_refine_plan: refining --(DONE)--> planning
t_refine_plan ==
    /\ state = "refining"
    /\ error = NULL  \* gate: no_error
    /\ state' = "planning"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_refine_error: refining --(DONE)--> error
t_refine_error ==
    /\ state = "refining"
    /\ error /= NULL  \* gate: has_error
    /\ state' = "error"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_error_step_retry: error --(DONE)--> executing
t_error_step_retry ==
    /\ state = "error"
    /\ (step_error_count = NULL \/ step_error_count < max_errors)  \* gate: step_can_retry
    /\ plan /= NULL  \* gate: has_plan
    /\ state' = "executing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_error_no_plan: error --(DONE)--> refining
t_error_no_plan ==
    /\ state = "error"
    /\ plan = NULL \/ step_count = NULL \/ step_count = 0  \* gate: no_plan
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_error_no_plan_maxiter: error --(DONE)--> complete
t_error_no_plan_maxiter ==
    /\ state = "error"
    /\ plan = NULL \/ step_count = NULL \/ step_count = 0  \* gate: no_plan
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_error_to_review: error --(DONE)--> reviewing
t_error_to_review ==
    /\ state = "error"
    /\ (step_error_count /= NULL /\ step_error_count >= max_errors)  \* gate: step_max_errors
    /\ state' = "reviewing"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_error_maxiter_complete: error --(DONE)--> complete
t_error_maxiter_complete ==
    /\ state = "error"
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ plan /= NULL  \* gate: has_plan
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_too_many_fails: reviewing --(DONE)--> evaluating
t_review_too_many_fails ==
    /\ state = "reviewing"
    /\ failed_steps /= NULL /\ Len(failed_steps) >= 3  \* gate: too_many_failed_steps
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_skip: reviewing --(DONE)--> stepping
t_review_skip ==
    /\ state = "reviewing"
    /\ review_decision = "skip"  \* gate: review_skip
    /\ step_index + 1 < step_count  \* gate: has_more_steps
    /\ state' = "stepping"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_skip_eval: reviewing --(DONE)--> evaluating
t_review_skip_eval ==
    /\ state = "reviewing"
    /\ review_decision = "skip"  \* gate: review_skip
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_replan: reviewing --(DONE)--> refining
t_review_replan ==
    /\ state = "reviewing"
    /\ review_decision = "replan"  \* gate: review_replan
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_replan_maxiter: reviewing --(DONE)--> evaluating
t_review_replan_maxiter ==
    /\ state = "reviewing"
    /\ review_decision = "replan"  \* gate: review_replan
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_invalid_skip: reviewing --(DONE)--> stepping
t_review_invalid_skip ==
    /\ state = "reviewing"
    /\ review_decision = NULL \/ (review_decision /= "skip" /\ review_decision /= "replan")  \* gate: review_invalid
    /\ step_index + 1 < step_count  \* gate: has_more_steps
    /\ state' = "stepping"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_invalid_eval: reviewing --(DONE)--> evaluating
t_review_invalid_eval ==
    /\ state = "reviewing"
    /\ review_decision = NULL \/ (review_decision /= "skip" /\ review_decision /= "replan")  \* gate: review_invalid
    /\ step_index + 1 >= step_count  \* gate: all_steps_done
    /\ state' = "evaluating"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_no_plan: reviewing --(DONE)--> refining
t_review_no_plan ==
    /\ state = "reviewing"
    /\ plan = NULL \/ step_count = NULL \/ step_count = 0  \* gate: no_plan
    /\ iteration < max_iterations  \* gate: within_iterations
    /\ state' = "refining"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_review_no_plan_maxiter: reviewing --(DONE)--> complete
t_review_no_plan_maxiter ==
    /\ state = "reviewing"
    /\ plan = NULL \/ step_count = NULL \/ step_count = 0  \* gate: no_plan
    /\ iteration >= max_iterations  \* gate: max_iterations_reached
    /\ state' = "complete"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "DONE")

\* t_recover: error --(RETRY)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "RETRY")

\* t_reset: * --(RESET)--> idle
t_reset ==
    /\ TRUE  \* from any state
    /\ state' = "idle"
    /\ api_key' = api_key
    /\ api_base' = api_base
    /\ model' = model
    /\ target' = target
    /\ workspace_path' = workspace_path
    /\ run_id' = run_id
    /\ run_dir' = run_dir
    /\ phase' = phase
    /\ blueprint_validated' = blueprint_validated
    /\ plan' = plan
    /\ current_step' = current_step
    /\ step_index' = step_index
    /\ step_count' = step_count
    /\ execution_log' = execution_log
    /\ artifacts' = artifacts
    /\ evaluation' = evaluation
    /\ score' = score
    /\ threshold' = threshold
    /\ feedback' = feedback
    /\ iteration' = iteration
    /\ max_iterations' = max_iterations
    /\ is_satisfied' = is_satisfied
    /\ error' = error
    /\ error_count' = error_count
    /\ max_errors' = max_errors
    /\ last_error' = last_error
    /\ step_error_count' = step_error_count
    /\ failed_steps' = failed_steps
    /\ review_decision' = review_decision
    /\ is_lpp_target' = is_lpp_target
    /\ lpp_validated' = lpp_validated
    /\ lpp_root' = lpp_root
    /\ raw_output' = raw_output
    /\ parsed_output' = parsed_output
    /\ parse_error' = parse_error
    /\ corrections' = corrections
    /\ corrections_approved' = corrections_approved
    /\ repair_attempts' = repair_attempts
    /\ max_repairs' = max_repairs
    /\ interactive_valid' = interactive_valid
    /\ interactive_feedback' = interactive_feedback
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t_start
    \/ t_submit_target
    \/ t_plan_ready
    \/ t_plan_error
    \/ t_exec_to_parse
    \/ t_exec_error
    \/ t_parse_ok_correct_step
    \/ t_parse_ok_step
    \/ t_parse_ok_correct_blueprint_validate
    \/ t_parse_ok_blueprint_validate
    \/ t_parse_ok_correct_impl_validate
    \/ t_parse_ok_impl_validate
    \/ t_parse_ok_correct_eval
    \/ t_parse_ok_eval
    \/ t_correct_to_step
    \/ t_correct_to_validate_blueprint
    \/ t_correct_to_validate_impl
    \/ t_correct_to_eval
    \/ t_parse_fail_retry
    \/ t_parse_fail_max
    \/ t_step_exec
    \/ t_step_validate_blueprint
    \/ t_step_validate_impl
    \/ t_step_eval
    \/ t_step_error
    \/ t_validate_blueprint_pass
    \/ t_validate_impl_pass
    \/ t_eval_interactive_pass
    \/ t_eval_interactive_fail
    \/ t_eval_interactive_maxiter
    \/ t_eval_interactive_error
    \/ t_validate_blueprint_fail
    \/ t_validate_impl_fail
    \/ t_validate_fail_maxiter
    \/ t_validate_error
    \/ t_eval_satisfied
    \/ t_eval_lpp_fail
    \/ t_eval_refine
    \/ t_eval_maxiter
    \/ t_eval_lpp_hard_fail
    \/ t_eval_error
    \/ t_refine_plan
    \/ t_refine_error
    \/ t_error_step_retry
    \/ t_error_no_plan
    \/ t_error_no_plan_maxiter
    \/ t_error_to_review
    \/ t_error_maxiter_complete
    \/ t_review_too_many_fails
    \/ t_review_skip
    \/ t_review_skip_eval
    \/ t_review_replan
    \/ t_review_replan_maxiter
    \/ t_review_invalid_skip
    \/ t_review_invalid_eval
    \/ t_review_no_plan
    \/ t_review_no_plan_maxiter
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