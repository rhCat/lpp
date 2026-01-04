"""
L++ Compiled Operator: Skill Contractor
Version: 1.7.0
Description: Autonomous L++ skill generator. Continuously iterates on logic to achieve coding targets with self-evaluation. Two-phase workflow: (1) Blueprint phase generates and validates JSON until TLC passes, (2) Implementation phase generates compute+interactive with auto-sanitization (fixes literal newlines in strings) and enhanced validation (content checks, AST parsing, import validation, structure checks). Features auto-correction of schema issues with logging. Enforces L++ schema v0.1.2 and build_rules.md for skill creation.

Auto-generated from JSON blueprint. Do not edit directly.
"""

from frame_py.lpp_core import (
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    TransitionTrace,
)


# ======================================================================
# BLUEPRINT CONSTANTS
# ======================================================================

BLUEPRINT_ID = 'skill_contractor'
BLUEPRINT_NAME = 'Skill Contractor'
BLUEPRINT_VERSION = '1.7.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = {'complete'}

STATES = {
    'idle': 'idle',  # Awaiting target assignment
    # Decomposing target into steps (L++ workflow if is_lpp_target)
    'planning': 'planning',
    'executing': 'executing',  # LLM generating step output
    # Parsing LLM output and applying auto-corrections for schema compliance
    'parsing': 'parsing',
    # Auto-corrections applied - logging for review (auto-approved unless critical)
    'correcting': 'correcting',
    'stepping': 'stepping',  # Advancing to next step
    'validating': 'validating',  # Validating L++ artifacts with build_skill.sh
    # Evaluating generated interactive.py with syntax and import checks
    'eval_interactive': 'eval_interactive',
    # Self-evaluating progress (includes L++ compliance check)
    'evaluating': 'evaluating',
    'refining': 'refining',  # Refining plan based on feedback
    'reviewing': 'reviewing',  # Reviewing failed step - skip or replan
    'complete': 'complete',  # Target achieved
    'error': 'error',  # Error occurred
}

GATES = {
    'has_target': 'target is not None and len(target) > 0',
    'has_plan': 'plan is not None',
    'has_more_steps': 'step_index + 1 < step_count',
    'all_steps_done': 'step_index + 1 >= step_count',
    'is_satisfied': 'is_satisfied == True',
    'not_satisfied': 'is_satisfied == False or is_satisfied is None',
    'within_iterations': 'iteration < max_iterations',
    'max_iterations_reached': 'iteration >= max_iterations',
    'above_threshold': 'score >= threshold',
    'below_threshold': 'score < threshold',
    'has_error': 'error is not None',
    'no_error': 'error is None',
    'can_retry_error': 'error_count < max_errors',
    'max_errors_reached': 'error_count >= max_errors',
    'has_target_for_recovery': 'target is not None and error_count < max_errors',
    'step_can_retry': '(step_error_count is None or step_error_count < max_errors)',
    'step_max_errors': '(step_error_count is not None and step_error_count >= max_errors)',
    'review_skip': 'review_decision == "skip"',
    'review_replan': 'review_decision == "replan"',
    'review_invalid': 'review_decision is None or (review_decision != "skip" and review_decision != "replan")',
    'no_plan': 'plan is None or step_count is None or step_count == 0',
    'too_many_failed_steps': 'failed_steps is not None and len(failed_steps) >= 3',
    'is_lpp_target': 'is_lpp_target == True',
    'not_lpp_target': 'is_lpp_target != True',
    'lpp_valid': 'lpp_validated == True',
    'lpp_invalid': 'is_lpp_target == True and lpp_validated != True',
    'lpp_ok': 'is_lpp_target != True or lpp_validated == True',
    'output_valid': 'parsed_output is not None and parse_error is None',
    'output_invalid': 'parse_error is not None',
    'can_repair': '(repair_attempts is None or repair_attempts < max_repairs)',
    'max_repairs_reached': '(repair_attempts is not None and repair_attempts >= max_repairs)',
    'has_raw_output': 'raw_output is not None and len(raw_output) > 0',
    'in_blueprint_phase': 'phase == "blueprint"',
    'in_implementation_phase': 'phase == "implementation"',
    'blueprint_validated': 'blueprint_validated == True',
    'blueprint_not_validated': 'blueprint_validated != True',
    'has_corrections': 'corrections is not None and len(corrections) > 0',
    'no_corrections': 'corrections is None or len(corrections) == 0',
    'corrections_approved': 'corrections_approved == True',
    'interactive_valid': 'interactive_valid == True',
    'interactive_invalid': 'interactive_valid != True',
}

DISPLAY_RULES = [
    {'gate': 'has_corrections',
        'template': '📝 AUTO-CORRECTED: {corrections} schema issues fixed - approved for validation'},
    {'gate': 'output_invalid',
        'template': '⚠️ PARSE ERROR (repair {repair_attempts}/{max_repairs}): {parse_error}'},
    {'gate': 'lpp_invalid',
        'template': 'L++ VALIDATION FAILED - refining to fix schema/build issues'},
    {'gate': 'lpp_valid', 'template': 'L++ VALIDATED: Schema v0.1.2 compliant, TLC passed'},
    {'gate': 'too_many_failed_steps',
        'template': 'WARNING: {failed_steps} steps failed - evaluating partial'},
    {'gate': 'step_max_errors',
        'template': 'REVIEWING: Step {step_index} failed {step_error_count}x - {review_decision}'},
    {'gate': 'has_error',
        'template': 'ERROR ({step_error_count}/{max_errors}): {error} - retrying step...'},
    {'gate': 'is_satisfied', 'template': 'COMPLETE: Score {score}/100'},
    {'gate': 'is_lpp_target',
        'template': 'L++ Mode | Step {step_index}/{step_count} | Iter {iteration}'},
    {'gate': 'has_plan', 'template': 'Step {step_index}/{step_count} | Iter {iteration} | Failed {failed_steps}'},
    {'template': 'Ready - submit a coding target'},
]

ACTIONS = {
    'init': {
        'type': 'compute',
        'compute_unit': 'agent:init',
        'output_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'workspace_path': 'workspace_path', 'run_id': 'run_id', 'run_dir': 'run_dir', 'phase': 'phase', 'blueprint_validated': 'blueprint_validated', 'threshold': 'threshold', 'max_iterations': 'max_iterations', 'iteration': 'iteration', 'execution_log': 'execution_log', 'artifacts': 'artifacts', 'error_count': 'error_count', 'max_errors': 'max_errors', 'step_error_count': 'step_error_count', 'failed_steps': 'failed_steps', 'is_lpp_target': 'is_lpp_target', 'lpp_validated': 'lpp_validated', 'lpp_root': 'lpp_root', 'repair_attempts': 'repair_attempts', 'max_repairs': 'max_repairs'},
    },
    'set_target': {
        'type': 'set',
        'target': 'target',
        'value_from': 'event.payload.target',
    },
    'detect_lpp_target': {
        'type': 'compute',
        'compute_unit': 'agent:detect_lpp_target',
        'input_map': {'target': 'target'},
        'output_map': {'is_lpp_target': 'is_lpp_target'},
    },
    'decompose': {
        'type': 'compute',
        'compute_unit': 'agent:decompose',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'target': 'target', 'workspace_path': 'workspace_path', 'run_dir': 'run_dir', 'feedback': 'feedback', 'is_lpp_target': 'is_lpp_target', 'lpp_root': 'lpp_root', 'iteration': 'iteration', 'phase': 'phase'},
        'output_map': {'plan': 'plan', 'step_count': 'step_count', 'step_index': 'step_index', 'current_step': 'current_step', 'error': 'error'},
    },
    'generate_step_output': {
        'type': 'compute',
        'compute_unit': 'agent:generate_step_output',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'target': 'target', 'plan': 'plan', 'current_step': 'current_step', 'step_index': 'step_index', 'workspace_path': 'workspace_path', 'run_dir': 'run_dir', 'execution_log': 'execution_log', 'is_lpp_target': 'is_lpp_target', 'lpp_root': 'lpp_root', 'feedback': 'feedback', 'iteration': 'iteration', 'parse_error': 'parse_error', 'raw_output': 'raw_output', 'repair_attempts': 'repair_attempts', 'phase': 'phase'},
        'output_map': {'raw_output': 'raw_output', 'error': 'error'},
    },
    'parse_and_sanitize': {
        'type': 'compute',
        'compute_unit': 'agent:parse_and_sanitize',
        'input_map': {'raw_output': 'raw_output', 'current_step': 'current_step', 'step_index': 'step_index', 'run_dir': 'run_dir', 'is_lpp_target': 'is_lpp_target', 'phase': 'phase'},
        'output_map': {'parsed_output': 'parsed_output', 'parse_error': 'parse_error', 'corrections': 'corrections'},
    },
    'approve_corrections': {
        'type': 'set',
        'target': 'corrections_approved',
        'value': True,
    },
    'log_corrections': {
        'type': 'compute',
        'compute_unit': 'agent:log_corrections',
        'input_map': {'corrections': 'corrections', 'run_dir': 'run_dir', 'step_index': 'step_index'},
        'output_map': {'corrections_approved': 'corrections_approved'},
    },
    'write_output': {
        'type': 'compute',
        'compute_unit': 'agent:write_output',
        'input_map': {'parsed_output': 'parsed_output', 'current_step': 'current_step', 'step_index': 'step_index', 'workspace_path': 'workspace_path', 'run_dir': 'run_dir', 'raw_output': 'raw_output', 'execution_log': 'execution_log', 'artifacts': 'artifacts'},
        'output_map': {'execution_log': 'execution_log', 'artifacts': 'artifacts', 'current_step': 'current_step', 'error': 'error'},
    },
    'incr_repair': {
        'type': 'compute',
        'compute_unit': 'agent:incr_repair',
        'input_map': {'repair_attempts': 'repair_attempts'},
        'output_map': {'repair_attempts': 'repair_attempts'},
    },
    'reset_repair': {
        'type': 'set',
        'target': 'repair_attempts',
        'value': 0,
    },
    'clear_parse_error': {
        'type': 'set',
        'target': 'parse_error',
    },
    'advance_step': {
        'type': 'compute',
        'compute_unit': 'agent:advance_step',
        'input_map': {'plan': 'plan', 'step_index': 'step_index', 'step_count': 'step_count', 'run_dir': 'run_dir'},
        'output_map': {'step_index': 'step_index', 'current_step': 'current_step'},
    },
    'validate_lpp': {
        'type': 'compute',
        'compute_unit': 'agent:validate_lpp',
        'input_map': {'workspace_path': 'workspace_path', 'run_dir': 'run_dir', 'artifacts': 'artifacts', 'lpp_root': 'lpp_root', 'phase': 'phase'},
        'output_map': {'lpp_validated': 'lpp_validated', 'blueprint_validated': 'blueprint_validated', 'feedback': 'feedback', 'error': 'error'},
    },
    'advance_phase': {
        'type': 'compute',
        'compute_unit': 'agent:advance_phase',
        'input_map': {'phase': 'phase', 'run_dir': 'run_dir'},
        'output_map': {'phase': 'phase'},
    },
    'evaluate': {
        'type': 'compute',
        'compute_unit': 'agent:evaluate',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'target': 'target', 'run_dir': 'run_dir', 'plan': 'plan', 'execution_log': 'execution_log', 'artifacts': 'artifacts', 'iteration': 'iteration', 'threshold': 'threshold', 'is_lpp_target': 'is_lpp_target', 'lpp_validated': 'lpp_validated'},
        'output_map': {'evaluation': 'evaluation', 'score': 'score', 'is_satisfied': 'is_satisfied', 'feedback': 'feedback', 'error': 'error'},
    },
    'evaluate_interactive': {
        'type': 'compute',
        'compute_unit': 'agent:evaluate_interactive',
        'input_map': {'run_dir': 'run_dir', 'artifacts': 'artifacts'},
        'output_map': {'interactive_valid': 'interactive_valid', 'interactive_feedback': 'interactive_feedback', 'error': 'error'},
    },
    'incr_iteration': {
        'type': 'compute',
        'compute_unit': 'agent:incr_iteration',
        'input_map': {'iteration': 'iteration'},
        'output_map': {'iteration': 'iteration'},
    },
    'reset_for_refine': {
        'type': 'compute',
        'compute_unit': 'agent:reset_for_refine',
        'output_map': {'step_index': 'step_index', 'current_step': 'current_step'},
    },
    'clear_error': {
        'type': 'set',
        'target': 'error',
    },
    'capture_error_feedback': {
        'type': 'compute',
        'compute_unit': 'agent:capture_error',
        'input_map': {'error': 'error', 'error_count': 'error_count', 'current_step': 'current_step', 'step_index': 'step_index', 'run_dir': 'run_dir'},
        'output_map': {'last_error': 'last_error', 'feedback': 'feedback', 'error_count': 'error_count'},
    },
    'reset_error_count': {
        'type': 'set',
        'target': 'error_count',
        'value': 0,
    },
    'prepare_recovery': {
        'type': 'compute',
        'compute_unit': 'agent:prepare_recovery',
        'input_map': {'last_error': 'last_error', 'feedback': 'feedback', 'plan': 'plan', 'step_index': 'step_index'},
        'output_map': {'feedback': 'feedback', 'error': 'error'},
    },
    'capture_step_error': {
        'type': 'compute',
        'compute_unit': 'agent:capture_step_error',
        'input_map': {'error': 'error', 'step_error_count': 'step_error_count', 'current_step': 'current_step', 'step_index': 'step_index', 'run_dir': 'run_dir'},
        'output_map': {'last_error': 'last_error', 'feedback': 'feedback', 'step_error_count': 'step_error_count'},
    },
    'reset_step_error_count': {
        'type': 'set',
        'target': 'step_error_count',
        'value': 0,
    },
    'review_failed_step': {
        'type': 'compute',
        'compute_unit': 'agent:review_failed_step',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'target': 'target', 'run_dir': 'run_dir', 'plan': 'plan', 'current_step': 'current_step', 'step_index': 'step_index', 'step_count': 'step_count', 'last_error': 'last_error', 'failed_steps': 'failed_steps', 'execution_log': 'execution_log'},
        'output_map': {'review_decision': 'review_decision', 'feedback': 'feedback', 'failed_steps': 'failed_steps'},
    },
    'skip_to_next_step': {
        'type': 'compute',
        'compute_unit': 'agent:skip_step',
        'input_map': {'plan': 'plan', 'step_index': 'step_index', 'step_count': 'step_count', 'run_dir': 'run_dir', 'failed_steps': 'failed_steps', 'current_step': 'current_step'},
        'output_map': {'step_index': 'step_index', 'current_step': 'current_step', 'failed_steps': 'failed_steps', 'step_error_count': 'step_error_count'},
    },
    'capture_parse_error': {
        'type': 'compute',
        'compute_unit': 'agent:capture_parse_error',
        'input_map': {'parse_error': 'parse_error', 'raw_output': 'raw_output', 'repair_attempts': 'repair_attempts', 'step_index': 'step_index', 'run_dir': 'run_dir'},
        'output_map': {'feedback': 'feedback', 'step_error_count': 'step_error_count'},
    },
    'copy_interactive_feedback': {
        'type': 'set',
        'target': 'feedback',
        'value_from': 'interactive_feedback',
    },
    'set_lpp_hard_fail': {
        'type': 'set',
        'target': 'error',
        'value': 'L++ HARD FAIL: Max iterations reached without passing ./utils/build_skill.sh --validate. Blueprint must be TLC-valid.',
    },
}

TRANSITIONS = [
    {
        'id': 't_start',
        'from': 'idle',
        'to': 'idle',
        'on_event': 'START',
        'gates': [],
        'actions': ['init'],
    },
    {
        'id': 't_submit_target',
        'from': 'idle',
        'to': 'planning',
        'on_event': 'SUBMIT',
        'gates': [],
        'actions': ['set_target', 'detect_lpp_target', 'decompose'],
    },
    {
        'id': 't_plan_ready',
        'from': 'planning',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['has_plan', 'no_error'],
        'actions': ['generate_step_output'],
    },
    {
        'id': 't_plan_error',
        'from': 'planning',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_error_feedback'],
    },
    {
        'id': 't_exec_to_parse',
        'from': 'executing',
        'to': 'parsing',
        'on_event': 'DONE',
        'gates': ['has_raw_output', 'no_error'],
        'actions': ['parse_and_sanitize'],
    },
    {
        'id': 't_exec_error',
        'from': 'executing',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_step_error'],
    },
    {
        'id': 't_parse_ok_correct_step',
        'from': 'parsing',
        'to': 'correcting',
        'on_event': 'DONE',
        'gates': ['output_valid', 'has_corrections', 'has_more_steps'],
        'actions': ['log_corrections'],
    },
    {
        'id': 't_parse_ok_step',
        'from': 'parsing',
        'to': 'stepping',
        'on_event': 'DONE',
        'gates': ['output_valid', 'no_corrections', 'has_more_steps'],
        'actions': ['write_output', 'reset_repair'],
    },
    {
        'id': 't_parse_ok_correct_blueprint_validate',
        'from': 'parsing',
        'to': 'correcting',
        'on_event': 'DONE',
        'gates': ['output_valid', 'has_corrections', 'all_steps_done', 'is_lpp_target', 'in_blueprint_phase'],
        'actions': ['log_corrections'],
    },
    {
        'id': 't_parse_ok_blueprint_validate',
        'from': 'parsing',
        'to': 'validating',
        'on_event': 'DONE',
        'gates': ['output_valid', 'no_corrections', 'all_steps_done', 'is_lpp_target', 'in_blueprint_phase'],
        'actions': ['write_output', 'reset_repair', 'validate_lpp'],
    },
    {
        'id': 't_parse_ok_correct_impl_validate',
        'from': 'parsing',
        'to': 'correcting',
        'on_event': 'DONE',
        'gates': ['output_valid', 'has_corrections', 'all_steps_done', 'is_lpp_target', 'in_implementation_phase'],
        'actions': ['log_corrections'],
    },
    {
        'id': 't_parse_ok_impl_validate',
        'from': 'parsing',
        'to': 'validating',
        'on_event': 'DONE',
        'gates': ['output_valid', 'no_corrections', 'all_steps_done', 'is_lpp_target', 'in_implementation_phase'],
        'actions': ['write_output', 'reset_repair', 'validate_lpp'],
    },
    {
        'id': 't_parse_ok_correct_eval',
        'from': 'parsing',
        'to': 'correcting',
        'on_event': 'DONE',
        'gates': ['output_valid', 'has_corrections', 'all_steps_done', 'not_lpp_target'],
        'actions': ['log_corrections'],
    },
    {
        'id': 't_parse_ok_eval',
        'from': 'parsing',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['output_valid', 'no_corrections', 'all_steps_done', 'not_lpp_target'],
        'actions': ['write_output', 'reset_repair', 'evaluate'],
    },
    {
        'id': 't_correct_to_step',
        'from': 'correcting',
        'to': 'stepping',
        'on_event': 'DONE',
        'gates': ['corrections_approved', 'has_more_steps'],
        'actions': ['write_output', 'reset_repair'],
    },
    {
        'id': 't_correct_to_validate_blueprint',
        'from': 'correcting',
        'to': 'validating',
        'on_event': 'DONE',
        'gates': ['corrections_approved', 'all_steps_done', 'is_lpp_target', 'in_blueprint_phase'],
        'actions': ['write_output', 'reset_repair', 'validate_lpp'],
    },
    {
        'id': 't_correct_to_validate_impl',
        'from': 'correcting',
        'to': 'validating',
        'on_event': 'DONE',
        'gates': ['corrections_approved', 'all_steps_done', 'is_lpp_target', 'in_implementation_phase'],
        'actions': ['write_output', 'reset_repair', 'validate_lpp'],
    },
    {
        'id': 't_correct_to_eval',
        'from': 'correcting',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['corrections_approved', 'all_steps_done', 'not_lpp_target'],
        'actions': ['write_output', 'reset_repair', 'evaluate'],
    },
    {
        'id': 't_parse_fail_retry',
        'from': 'parsing',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['output_invalid', 'can_repair'],
        'actions': ['capture_parse_error', 'incr_repair', 'generate_step_output'],
    },
    {
        'id': 't_parse_fail_max',
        'from': 'parsing',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['output_invalid', 'max_repairs_reached'],
        'actions': ['capture_step_error'],
    },
    {
        'id': 't_step_exec',
        'from': 'stepping',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['has_more_steps', 'no_error'],
        'actions': ['advance_step', 'reset_step_error_count', 'reset_repair', 'clear_parse_error', 'generate_step_output'],
    },
    {
        'id': 't_step_validate_blueprint',
        'from': 'stepping',
        'to': 'validating',
        'on_event': 'DONE',
        'gates': ['all_steps_done', 'no_error', 'is_lpp_target', 'in_blueprint_phase'],
        'actions': ['validate_lpp'],
    },
    {
        'id': 't_step_validate_impl',
        'from': 'stepping',
        'to': 'validating',
        'on_event': 'DONE',
        'gates': ['all_steps_done', 'no_error', 'is_lpp_target', 'in_implementation_phase'],
        'actions': ['validate_lpp'],
    },
    {
        'id': 't_step_eval',
        'from': 'stepping',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['all_steps_done', 'no_error', 'not_lpp_target'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_step_error',
        'from': 'stepping',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_error_feedback'],
    },
    {
        'id': 't_validate_blueprint_pass',
        'from': 'validating',
        'to': 'planning',
        'on_event': 'DONE',
        'gates': ['blueprint_validated', 'no_error', 'in_blueprint_phase'],
        'actions': ['advance_phase', 'decompose'],
    },
    {
        'id': 't_validate_impl_pass',
        'from': 'validating',
        'to': 'eval_interactive',
        'on_event': 'DONE',
        'gates': ['lpp_valid', 'no_error', 'in_implementation_phase'],
        'actions': ['evaluate_interactive'],
    },
    {
        'id': 't_eval_interactive_pass',
        'from': 'eval_interactive',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['interactive_valid', 'no_error'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_eval_interactive_fail',
        'from': 'eval_interactive',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['interactive_invalid', 'within_iterations'],
        'actions': ['copy_interactive_feedback', 'incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_eval_interactive_maxiter',
        'from': 'eval_interactive',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['interactive_invalid', 'max_iterations_reached'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_eval_interactive_error',
        'from': 'eval_interactive',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_error_feedback'],
    },
    {
        'id': 't_validate_blueprint_fail',
        'from': 'validating',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['blueprint_not_validated', 'within_iterations', 'in_blueprint_phase'],
        'actions': ['incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_validate_impl_fail',
        'from': 'validating',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['lpp_invalid', 'within_iterations', 'in_implementation_phase'],
        'actions': ['incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_validate_fail_maxiter',
        'from': 'validating',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['lpp_invalid', 'max_iterations_reached'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_validate_error',
        'from': 'validating',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_error_feedback'],
    },
    {
        'id': 't_eval_satisfied',
        'from': 'evaluating',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['is_satisfied', 'lpp_ok', 'no_error'],
        'actions': [],
    },
    {
        'id': 't_eval_lpp_fail',
        'from': 'evaluating',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['is_satisfied', 'lpp_invalid', 'within_iterations', 'no_error'],
        'actions': ['incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_eval_refine',
        'from': 'evaluating',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['not_satisfied', 'within_iterations', 'no_error'],
        'actions': ['incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_eval_maxiter',
        'from': 'evaluating',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['max_iterations_reached', 'lpp_ok'],
        'actions': [],
    },
    {
        'id': 't_eval_lpp_hard_fail',
        'from': 'evaluating',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['max_iterations_reached', 'lpp_invalid'],
        'actions': ['set_lpp_hard_fail', 'capture_error_feedback'],
    },
    {
        'id': 't_eval_error',
        'from': 'evaluating',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_error_feedback'],
    },
    {
        'id': 't_refine_plan',
        'from': 'refining',
        'to': 'planning',
        'on_event': 'DONE',
        'gates': ['no_error'],
        'actions': ['decompose'],
    },
    {
        'id': 't_refine_error',
        'from': 'refining',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': ['capture_error_feedback'],
    },
    {
        'id': 't_error_step_retry',
        'from': 'error',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['step_can_retry', 'has_plan'],
        'actions': ['clear_error', 'reset_repair', 'generate_step_output'],
    },
    {
        'id': 't_error_no_plan',
        'from': 'error',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['no_plan', 'within_iterations'],
        'actions': ['clear_error', 'incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_error_no_plan_maxiter',
        'from': 'error',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['no_plan', 'max_iterations_reached'],
        'actions': [],
    },
    {
        'id': 't_error_to_review',
        'from': 'error',
        'to': 'reviewing',
        'on_event': 'DONE',
        'gates': ['step_max_errors'],
        'actions': ['clear_error', 'review_failed_step'],
    },
    {
        'id': 't_error_maxiter_complete',
        'from': 'error',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['max_iterations_reached', 'has_plan'],
        'actions': [],
    },
    {
        'id': 't_review_too_many_fails',
        'from': 'reviewing',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['too_many_failed_steps'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_review_skip',
        'from': 'reviewing',
        'to': 'stepping',
        'on_event': 'DONE',
        'gates': ['review_skip', 'has_more_steps'],
        'actions': ['reset_repair', 'skip_to_next_step'],
    },
    {
        'id': 't_review_skip_eval',
        'from': 'reviewing',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['review_skip', 'all_steps_done'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_review_replan',
        'from': 'reviewing',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['review_replan', 'within_iterations'],
        'actions': ['incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_review_replan_maxiter',
        'from': 'reviewing',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['review_replan', 'max_iterations_reached'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_review_invalid_skip',
        'from': 'reviewing',
        'to': 'stepping',
        'on_event': 'DONE',
        'gates': ['review_invalid', 'has_more_steps'],
        'actions': ['reset_repair', 'skip_to_next_step'],
    },
    {
        'id': 't_review_invalid_eval',
        'from': 'reviewing',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['review_invalid', 'all_steps_done'],
        'actions': ['evaluate'],
    },
    {
        'id': 't_review_no_plan',
        'from': 'reviewing',
        'to': 'refining',
        'on_event': 'DONE',
        'gates': ['no_plan', 'within_iterations'],
        'actions': ['incr_iteration', 'reset_for_refine'],
    },
    {
        'id': 't_review_no_plan_maxiter',
        'from': 'reviewing',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['no_plan', 'max_iterations_reached'],
        'actions': [],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RETRY',
        'gates': [],
        'actions': ['clear_error', 'reset_error_count', 'reset_step_error_count', 'reset_repair'],
    },
    {
        'id': 't_reset',
        'from': '*',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': [],
    },
]


# ======================================================================
# HELPER FUNCTIONS
# ======================================================================

def _resolve_path(path: str, data: dict):
    """Resolve a dotted path in a dictionary."""
    parts = path.split('.')
    obj = data
    for part in parts:
        if isinstance(obj, dict):
            obj = obj.get(part)
        else:
            return None
        if obj is None:
            return None
    return obj


# ======================================================================
# COMPILED OPERATOR
# ======================================================================

class Operator:
    """
    Compiled L++ Operator: Skill Contractor
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'api_key': None, 'api_base': None, 'model': None, 'target': None, 'workspace_path': None, 'run_id': None, 'run_dir': None, 'phase': None, 'blueprint_validated': None, 'plan': None, 'current_step': None, 'step_index': None, 'step_count': None, 'execution_log': None, 'artifacts': None, 'evaluation': None, 'score': None, 'threshold': None, 'feedback': None, 'iteration': None, 'max_iterations': None,
                        'is_satisfied': None, 'error': None, 'error_count': None, 'max_errors': None, 'last_error': None, 'step_error_count': None, 'failed_steps': None, 'review_decision': None, 'is_lpp_target': None, 'lpp_validated': None, 'lpp_root': None, 'raw_output': None, 'parsed_output': None, 'parse_error': None, 'corrections': None, 'corrections_approved': None, 'repair_attempts': None, 'max_repairs': None, 'interactive_valid': None, 'interactive_feedback': None}
        self.traces: list[TransitionTrace] = []
        self.compute_registry = compute_registry or {}

    @property
    def state(self) -> str:
        return self.context.get('_state', ENTRY_STATE)

    @property
    def is_terminal(self) -> bool:
        return self.state in TERMINAL_STATES

    def dispatch(self, event_name: str, payload: dict = None):
        """
        Dispatch an event to the operator.

        Args:
            event_name: Name of the event
            payload: Event payload data

        Returns:
            Tuple of (success, new_state, error)
        """
        payload = payload or {}
        current = self.state

        # Check terminal
        if self.is_terminal:
            return False, current, 'Already in terminal state'

        # Build evaluation scope
        scope = dict(self.context)
        scope['event'] = {'name': event_name, 'payload': payload}

        # Find matching transition (checks gates)
        trans = None
        for t in TRANSITIONS:
            if t['on_event'] != event_name:
                continue
            if t['from'] != '*' and t['from'] != current:
                continue
            # Check gates
            gates_pass = True
            for gate_id in t.get('gates', []):
                expr = GATES.get(gate_id, 'True')
                gate_result, _ = atom_EVALUATE(expr, scope)
                if not gate_result:
                    gates_pass = False
                    break
            if gates_pass:
                trans = t
                break

        if not trans:
            return False, current, f'No transition for {event_name}'

        # Execute actions
        for action_id in trans['actions']:
            action = ACTIONS.get(action_id)
            if not action:
                continue

            if action['type'] == 'set':
                # MUTATE
                target = action.get('target')
                if action.get('value') is not None:
                    value = action['value']
                elif action.get('value_from'):
                    value = _resolve_path(action['value_from'], scope)
                else:
                    value = None
                self.context, _ = atom_MUTATE(self.context, target, value)
                scope.update(self.context)  # Sync scope for chained actions

            elif action['type'] == 'compute':
                # DISPATCH
                unit = action.get('compute_unit', '')
                parts = unit.split(':')
                if len(parts) == 2:
                    sys_id, op_id = parts
                    inp = {
                        k: _resolve_path(v, scope)
                        for k, v in action.get('input_map', {}).items()
                    }
                    result, _ = atom_DISPATCH(
                        sys_id, op_id, inp, self.compute_registry
                    )
                    for ctx_path, res_key in action.get('output_map', {}).items():
                        if res_key in result:
                            self.context, _ = atom_MUTATE(
                                self.context, ctx_path, result[res_key]
                            )
                    # Sync scope for chained actions
                    scope.update(self.context)

        # TRANSITION
        (new_state, trace), _ = atom_TRANSITION(current, trans['to'])
        self.context, _ = atom_MUTATE(self.context, '_state', new_state)
        self.traces.append(trace)

        return True, new_state, None

    def get(self, path: str):
        """Get a value from context by path."""
        return _resolve_path(path, self.context)

    def set(self, path: str, value):
        """Set a value in context by path."""
        self.context, _ = atom_MUTATE(self.context, path, value)

    def display(self) -> str:
        """Evaluate display rules and return formatted string."""
        for rule in DISPLAY_RULES:
            gate = rule.get('gate')
            if gate:
                expr = GATES.get(gate, 'False')
                gate_result, _ = atom_EVALUATE(expr, self.context)
                if not gate_result:
                    continue
            # Gate passed or no gate, format template
            template = rule.get('template', '')
            try:
                return template.format(**self.context)
            except (KeyError, ValueError):
                return template
        return ''

    def reset(self):
        """Reset to initial state."""
        self.context = {'_state': ENTRY_STATE, 'api_key': None, 'api_base': None, 'model': None, 'target': None, 'workspace_path': None, 'run_id': None, 'run_dir': None, 'phase': None, 'blueprint_validated': None, 'plan': None, 'current_step': None, 'step_index': None, 'step_count': None, 'execution_log': None, 'artifacts': None, 'evaluation': None, 'score': None, 'threshold': None, 'feedback': None, 'iteration': None, 'max_iterations': None,
                        'is_satisfied': None, 'error': None, 'error_count': None, 'max_errors': None, 'last_error': None, 'step_error_count': None, 'failed_steps': None, 'review_decision': None, 'is_lpp_target': None, 'lpp_validated': None, 'lpp_root': None, 'raw_output': None, 'parsed_output': None, 'parse_error': None, 'corrections': None, 'corrections_approved': None, 'repair_attempts': None, 'max_repairs': None, 'interactive_valid': None, 'interactive_feedback': None}
        self.traces = []

    def save_state(self, path: str = None):
        """
        Save current state to JSON file.

        Args:
            path: File path (default: ./states/{id}.json)

        Returns:
            Path where state was saved
        """
        import json
        from pathlib import Path

        if not path:
            states_dir = Path('./states')
            states_dir.mkdir(exist_ok=True)
            path = states_dir / f'{BLUEPRINT_ID}.json'
        else:
            path = Path(path)
            path.parent.mkdir(parents=True, exist_ok=True)

        state_data = {
            'blueprint_id': BLUEPRINT_ID,
            'blueprint_version': BLUEPRINT_VERSION,
            'context': self.context,
            'traces': [
                {
                    'timestamp': t.timestamp.isoformat(),
                    'from_id': t.from_id,
                    'to_id': t.to_id,
                }
                for t in self.traces
            ]
        }

        with open(path, 'w') as f:
            json.dump(state_data, f, indent=2)

        return str(path)

    def load_state(self, path: str = None) -> bool:
        """
        Load state from JSON file.

        Args:
            path: File path (default: ./states/{id}.json)

        Returns:
            True if loaded successfully, False otherwise
        """
        import json
        from pathlib import Path
        from datetime import datetime, timezone

        if not path:
            path = Path('./states') / f'{BLUEPRINT_ID}.json'
        else:
            path = Path(path)

        if not path.exists():
            return False

        try:
            with open(path, 'r') as f:
                state_data = json.load(f)

            # Validate blueprint ID matches
            if state_data.get('blueprint_id') != BLUEPRINT_ID:
                print(
                    f'[L++ WARNING] Blueprint ID mismatch: {state_data.get("blueprint_id")}')
                return False

            self.context = state_data.get('context', {})

            # Restore traces
            self.traces = []
            for t in state_data.get('traces', []):
                self.traces.append(TransitionTrace(
                    timestamp=datetime.fromisoformat(
                        t['timestamp']
                    ).replace(tzinfo=timezone.utc),
                    from_id=t['from_id'],
                    to_id=t['to_id'],
                ))

            return True
        except Exception as e:
            print(f'[L++ ERROR] Failed to load state: {e}')
            return False


def create_operator(compute_registry: dict = None) -> Operator:
    """Factory function to create a new Operator instance."""
    return Operator(compute_registry)


if __name__ == '__main__':
    print('L++ Compiled Operator: Skill Contractor')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
