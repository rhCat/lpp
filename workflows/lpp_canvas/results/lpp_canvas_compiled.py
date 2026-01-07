"""
L++ Compiled Operator: L++ Canvas
Version: 1.0.0
Description: Higher-assembly blueprint studio for creating, reviewing, auditing, simulating, and editing L++ blueprints with LLM assistance and interactive GUI

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

BLUEPRINT_ID = 'lpp_canvas'
BLUEPRINT_NAME = 'L++ Canvas'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded
    'loaded': 'loaded',  # Blueprint loaded and ready
    'creating': 'creating',  # Creating new blueprint from scratch
    'editing': 'editing',  # Editing selected node
    'reviewing': 'reviewing',  # Reviewing and auditing blueprint
    'validating': 'validating',  # Running TLC validation
    'analyzing': 'analyzing',  # Analyzing paths and states
    'simulating': 'simulating',  # Simulating user walkthrough
    'clustering': 'clustering',  # Computing clusters and dependencies
    'llm_assist': 'llm_assist',  # Getting LLM assistance
    'generating': 'generating',  # Generating outputs (graph, mermaid)
    'saving': 'saving',  # Saving blueprint to file
    'error': 'error',  # Error state
}

GATES = {
    'g_llm_enabled': 'llm_enabled == True and api_key != None',
    'g_is_dirty': 'is_dirty == True',
    'g_has_blueprint': 'blueprint != None',
    'g_load_failed': 'error != None',
    'g_tlc_passed': 'tlc_passed == True',
    'g_has_selection': 'selected_node != None',
    'g_sim_not_terminal': 'sim_state != None',
    'g_has_prompt': 'prompt != None',
    'g_sim_step_limit': 'sim_step_count < 1000',
    'g_has_available_events': 'sim_available_events != None',
}

DISPLAY_RULES = [
]

ACTIONS = {
    'a_init_new': {
        'type': 'compute',
        'compute_unit': 'canvas:init_new',
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty', 'mode': 'mode'},
    },
    'a_load_blueprint': {
        'type': 'compute',
        'compute_unit': 'canvas:load_blueprint',
        'input_map': {'path': 'blueprint_path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'error': 'error'},
    },
    'a_create_blueprint': {
        'type': 'compute',
        'compute_unit': 'canvas:create_blueprint',
        'input_map': {'name': 'prompt', 'blueprint': 'blueprint'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_select_node': {
        'type': 'compute',
        'compute_unit': 'canvas:select_node',
        'input_map': {'blueprint': 'blueprint', 'node_id': 'selected_node', 'node_type': 'selected_type'},
        'output_map': {'node_data': 'node_data', 'edit_buffer': 'edit_buffer'},
    },
    'a_apply_edit': {
        'type': 'compute',
        'compute_unit': 'canvas:apply_edit',
        'input_map': {'blueprint': 'blueprint', 'node_id': 'selected_node', 'node_type': 'selected_type', 'edit_buffer': 'edit_buffer'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_clear_edit': {
        'type': 'set',
        'target': 'edit_buffer',
    },
    'a_delete_node': {
        'type': 'compute',
        'compute_unit': 'canvas:delete_node',
        'input_map': {'blueprint': 'blueprint', 'node_id': 'selected_node', 'node_type': 'selected_type'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_add_state': {
        'type': 'compute',
        'compute_unit': 'canvas:add_state',
        'input_map': {'blueprint': 'blueprint', 'state_data': 'edit_buffer'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_add_transition': {
        'type': 'compute',
        'compute_unit': 'canvas:add_transition',
        'input_map': {'blueprint': 'blueprint', 'transition_data': 'edit_buffer'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_add_gate': {
        'type': 'compute',
        'compute_unit': 'canvas:add_gate',
        'input_map': {'blueprint': 'blueprint', 'gate_data': 'edit_buffer'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_add_action': {
        'type': 'compute',
        'compute_unit': 'canvas:add_action',
        'input_map': {'blueprint': 'blueprint', 'action_data': 'edit_buffer'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_run_tlc': {
        'type': 'compute',
        'compute_unit': 'canvas:run_tlc',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'tlc_result': 'tlc_result', 'tlc_errors': 'tlc_errors', 'tlc_passed': 'tlc_passed', 'error': 'error'},
    },
    'a_analyze_paths': {
        'type': 'compute',
        'compute_unit': 'canvas:analyze_paths',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'paths': 'paths', 'path_count': 'path_count', 'states_list': 'states_list', 'state_count': 'state_count', 'reachability': 'reachability', 'deadlocks': 'deadlocks'},
    },
    'a_init_sim': {
        'type': 'compute',
        'compute_unit': 'canvas:init_simulation',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'sim_history': 'sim_history', 'sim_available_events': 'sim_available_events', 'sim_step_count': 'sim_step_count'},
    },
    'a_sim_step': {
        'type': 'compute',
        'compute_unit': 'canvas:sim_step',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'sim_history': 'sim_history', 'event': 'prompt'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'sim_history': 'sim_history', 'sim_available_events': 'sim_available_events', 'sim_step_count': 'sim_step_count'},
    },
    'a_sim_dispatch': {
        'type': 'compute',
        'compute_unit': 'canvas:sim_dispatch',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'event': 'prompt', 'payload': 'edit_buffer'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'sim_history': 'sim_history', 'sim_available_events': 'sim_available_events', 'sim_step_count': 'sim_step_count'},
    },
    'a_sim_reset': {
        'type': 'compute',
        'compute_unit': 'canvas:init_simulation',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'sim_history': 'sim_history', 'sim_available_events': 'sim_available_events', 'sim_step_count': 'sim_step_count'},
    },
    'a_compute_clusters': {
        'type': 'compute',
        'compute_unit': 'canvas:compute_clusters',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'clusters': 'clusters', 'dependencies': 'dependencies', 'sorted_states': 'sorted_states'},
    },
    'a_start_review': {
        'type': 'compute',
        'compute_unit': 'canvas:start_review',
        'input_map': {'blueprint': 'blueprint', 'review_notes': 'review_notes'},
        'output_map': {'review_notes': 'review_notes', 'review_status': 'review_status', 'coverage': 'coverage'},
    },
    'a_add_note': {
        'type': 'compute',
        'compute_unit': 'canvas:add_note',
        'input_map': {'review_notes': 'review_notes', 'note': 'prompt', 'node_id': 'selected_node'},
        'output_map': {'review_notes': 'review_notes'},
    },
    'a_set_approved': {
        'type': 'set',
        'target': 'review_status',
        'value': 'approved',
    },
    'a_set_rejected': {
        'type': 'set',
        'target': 'review_status',
        'value': 'rejected',
    },
    'a_add_audit': {
        'type': 'compute',
        'compute_unit': 'canvas:add_audit',
        'input_map': {'audit_log': 'audit_log', 'action': 'mode', 'node_id': 'selected_node', 'node_type': 'selected_type'},
        'output_map': {'audit_log': 'audit_log'},
    },
    'a_llm_query': {
        'type': 'compute',
        'compute_unit': 'canvas:llm_query',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'blueprint': 'blueprint', 'prompt': 'prompt', 'mode': 'mode', 'selected_node': 'selected_node'},
        'output_map': {'llm_response': 'llm_response', 'suggestions': 'suggestions', 'error': 'error'},
    },
    'a_apply_llm': {
        'type': 'compute',
        'compute_unit': 'canvas:apply_llm',
        'input_map': {'blueprint': 'blueprint', 'suggestions': 'suggestions'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty'},
    },
    'a_clear_llm': {
        'type': 'set',
        'target': 'llm_response',
    },
    'a_set_mode_create': {
        'type': 'set',
        'target': 'mode',
        'value': 'create',
    },
    'a_set_mode_edit': {
        'type': 'set',
        'target': 'mode',
        'value': 'edit',
    },
    'a_generate_outputs': {
        'type': 'compute',
        'compute_unit': 'canvas:generate_outputs',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'graph_html': 'graph_html', 'mermaid': 'mermaid'},
    },
    'a_save_blueprint': {
        'type': 'compute',
        'compute_unit': 'canvas:save_blueprint',
        'input_map': {'blueprint': 'blueprint', 'path': 'blueprint_path'},
        'output_map': {'error': 'error'},
    },
    'a_clear_dirty': {
        'type': 'set',
        'target': 'is_dirty',
        'value': False,
    },
    'a_set_error': {
        'type': 'set',
        'target': 'error',
        'value_from': 'error',
    },
    'a_clear_error': {
        'type': 'set',
        'target': 'error',
    },
    'a_clear': {
        'type': 'compute',
        'compute_unit': 'canvas:clear_all',
        'output_map': {'blueprint': 'blueprint', 'blueprint_json': 'blueprint_json', 'is_dirty': 'is_dirty', 'error': 'error'},
    },
}

TRANSITIONS = [
    {
        'id': 't_new',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'NEW',
        'gates': [],
        'actions': ['a_init_new'],
    },
    {
        'id': 't_load',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['a_load_blueprint'],
    },
    {
        'id': 't_load_err',
        'from': 'idle',
        'to': 'error',
        'on_event': 'LOAD',
        'gates': ['g_load_failed'],
        'actions': ['a_set_error'],
    },
    {
        'id': 't_set_bp',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'SET_BLUEPRINT',
        'gates': ['g_has_blueprint'],
        'actions': [],
    },
    {
        'id': 't_set_bp_any',
        'from': '*',
        'to': 'loaded',
        'on_event': 'SET_BLUEPRINT',
        'gates': ['g_has_blueprint'],
        'actions': [],
    },
    {
        'id': 't_reload',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['a_load_blueprint'],
    },
    {
        'id': 't_create_done',
        'from': 'creating',
        'to': 'loaded',
        'on_event': 'CREATE',
        'gates': [],
        'actions': ['a_create_blueprint'],
    },
    {
        'id': 't_create_llm',
        'from': 'creating',
        'to': 'llm_assist',
        'on_event': 'LLM_ASSIST',
        'gates': ['g_llm_enabled'],
        'actions': ['a_set_mode_create'],
    },
    {
        'id': 't_create_cancel',
        'from': 'creating',
        'to': 'idle',
        'on_event': 'CANCEL',
        'gates': [],
        'actions': ['a_clear'],
    },
    {
        'id': 't_select',
        'from': 'loaded',
        'to': 'editing',
        'on_event': 'SELECT',
        'gates': ['g_has_selection'],
        'actions': ['a_select_node'],
    },
    {
        'id': 't_review',
        'from': 'loaded',
        'to': 'reviewing',
        'on_event': 'REVIEW',
        'gates': [],
        'actions': ['a_start_review'],
    },
    {
        'id': 't_validate',
        'from': 'loaded',
        'to': 'validating',
        'on_event': 'VALIDATE',
        'gates': [],
        'actions': ['a_run_tlc'],
    },
    {
        'id': 't_analyze',
        'from': 'loaded',
        'to': 'analyzing',
        'on_event': 'ANALYZE',
        'gates': [],
        'actions': ['a_analyze_paths'],
    },
    {
        'id': 't_simulate',
        'from': 'loaded',
        'to': 'simulating',
        'on_event': 'SIMULATE',
        'gates': [],
        'actions': ['a_init_sim'],
    },
    {
        'id': 't_cluster',
        'from': 'loaded',
        'to': 'clustering',
        'on_event': 'CLUSTER',
        'gates': [],
        'actions': ['a_compute_clusters'],
    },
    {
        'id': 't_generate',
        'from': 'loaded',
        'to': 'generating',
        'on_event': 'GENERATE',
        'gates': [],
        'actions': ['a_generate_outputs'],
    },
    {
        'id': 't_llm_loaded',
        'from': 'loaded',
        'to': 'llm_assist',
        'on_event': 'LLM_ASSIST',
        'gates': ['g_llm_enabled'],
        'actions': ['a_set_mode_edit'],
    },
    {
        'id': 't_save',
        'from': 'loaded',
        'to': 'saving',
        'on_event': 'SAVE',
        'gates': ['g_is_dirty'],
        'actions': ['a_save_blueprint'],
    },
    {
        'id': 't_close',
        'from': 'loaded',
        'to': 'idle',
        'on_event': 'CLOSE',
        'gates': [],
        'actions': ['a_clear'],
    },
    {
        'id': 't_edit_apply',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'APPLY',
        'gates': [],
        'actions': ['a_apply_edit', 'a_add_audit'],
    },
    {
        'id': 't_edit_cancel',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'CANCEL',
        'gates': [],
        'actions': ['a_clear_edit'],
    },
    {
        'id': 't_edit_llm',
        'from': 'editing',
        'to': 'llm_assist',
        'on_event': 'LLM_ASSIST',
        'gates': ['g_llm_enabled'],
        'actions': ['a_set_mode_edit'],
    },
    {
        'id': 't_edit_delete',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'DELETE',
        'gates': [],
        'actions': ['a_delete_node', 'a_add_audit'],
    },
    {
        'id': 't_add_state',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'ADD_STATE',
        'gates': [],
        'actions': ['a_add_state', 'a_add_audit'],
    },
    {
        'id': 't_add_trans',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'ADD_TRANSITION',
        'gates': [],
        'actions': ['a_add_transition', 'a_add_audit'],
    },
    {
        'id': 't_add_gate',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'ADD_GATE',
        'gates': [],
        'actions': ['a_add_gate', 'a_add_audit'],
    },
    {
        'id': 't_add_action',
        'from': 'editing',
        'to': 'loaded',
        'on_event': 'ADD_ACTION',
        'gates': [],
        'actions': ['a_add_action', 'a_add_audit'],
    },
    {
        'id': 't_review_note',
        'from': 'reviewing',
        'to': 'reviewing',
        'on_event': 'ADD_NOTE',
        'gates': ['g_has_prompt'],
        'actions': ['a_add_note'],
    },
    {
        'id': 't_review_approve',
        'from': 'reviewing',
        'to': 'loaded',
        'on_event': 'APPROVE',
        'gates': [],
        'actions': ['a_set_approved'],
    },
    {
        'id': 't_review_reject',
        'from': 'reviewing',
        'to': 'loaded',
        'on_event': 'REJECT',
        'gates': [],
        'actions': ['a_set_rejected'],
    },
    {
        'id': 't_review_done',
        'from': 'reviewing',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_validate_done',
        'from': 'validating',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_validate_to_gen',
        'from': 'validating',
        'to': 'generating',
        'on_event': 'GENERATE',
        'gates': ['g_tlc_passed'],
        'actions': ['a_generate_outputs'],
    },
    {
        'id': 't_validate_err',
        'from': 'validating',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['a_set_error'],
    },
    {
        'id': 't_analyze_done',
        'from': 'analyzing',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_sim_step',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'STEP',
        'gates': ['g_sim_not_terminal', 'g_sim_step_limit', 'g_has_available_events'],
        'actions': ['a_sim_step'],
    },
    {
        'id': 't_sim_event',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'DISPATCH',
        'gates': ['g_sim_not_terminal', 'g_sim_step_limit'],
        'actions': ['a_sim_dispatch'],
    },
    {
        'id': 't_sim_reset',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'RESET',
        'gates': ['g_has_blueprint'],
        'actions': ['a_sim_reset'],
    },
    {
        'id': 't_sim_done',
        'from': 'simulating',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_cluster_done',
        'from': 'clustering',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_llm_done',
        'from': 'llm_assist',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_llm_apply',
        'from': 'llm_assist',
        'to': 'loaded',
        'on_event': 'APPLY',
        'gates': [],
        'actions': ['a_apply_llm', 'a_add_audit'],
    },
    {
        'id': 't_llm_cancel',
        'from': 'llm_assist',
        'to': 'loaded',
        'on_event': 'CANCEL',
        'gates': [],
        'actions': ['a_clear_llm'],
    },
    {
        'id': 't_llm_query',
        'from': 'llm_assist',
        'to': 'llm_assist',
        'on_event': 'QUERY',
        'gates': ['g_has_prompt', 'g_llm_enabled'],
        'actions': ['a_llm_query'],
    },
    {
        'id': 't_generate_done',
        'from': 'generating',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_save_done',
        'from': 'saving',
        'to': 'loaded',
        'on_event': 'DONE',
        'gates': [],
        'actions': ['a_clear_dirty'],
    },
    {
        'id': 't_save_err',
        'from': 'saving',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['a_set_error'],
    },
    {
        'id': 't_err_retry',
        'from': 'error',
        'to': 'loaded',
        'on_event': 'RETRY',
        'gates': ['g_has_blueprint'],
        'actions': ['a_clear_error'],
    },
    {
        'id': 't_err_reset',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['a_clear'],
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
    Compiled L++ Operator: L++ Canvas
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_json': None, 'is_dirty': None, 'mode': None, 'llm_enabled': None, 'api_key': None, 'api_base': None, 'model': None, 'prompt': None, 'llm_response': None, 'suggestions': None, 'selected_node': None, 'selected_type': None, 'node_data': None, 'edit_buffer': None, 'tlc_result': None, 'tlc_errors': None, 'tlc_passed': None, 'paths': None, 'path_count': None, 'states_list': None, 'state_count': None, 'reachability': None, 'deadlocks': None, 'sim_state': None, 'sim_context': None, 'sim_history': None, 'sim_available_events': None, 'sim_step_count': None, 'clusters': None, 'dependencies': None, 'sorted_states': None, 'audit_log': None, 'review_notes': None, 'review_status': None, 'coverage': None, 'graph_html': None, 'mermaid': None, 'error': None}
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
                    scope.update(self.context)  # Sync scope for chained actions

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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_json': None, 'is_dirty': None, 'mode': None, 'llm_enabled': None, 'api_key': None, 'api_base': None, 'model': None, 'prompt': None, 'llm_response': None, 'suggestions': None, 'selected_node': None, 'selected_type': None, 'node_data': None, 'edit_buffer': None, 'tlc_result': None, 'tlc_errors': None, 'tlc_passed': None, 'paths': None, 'path_count': None, 'states_list': None, 'state_count': None, 'reachability': None, 'deadlocks': None, 'sim_state': None, 'sim_context': None, 'sim_history': None, 'sim_available_events': None, 'sim_step_count': None, 'clusters': None, 'dependencies': None, 'sorted_states': None, 'audit_log': None, 'review_notes': None, 'review_status': None, 'coverage': None, 'graph_html': None, 'mermaid': None, 'error': None}
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
                print(f'[L++ WARNING] Blueprint ID mismatch: {state_data.get("blueprint_id")}')
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
    print('L++ Compiled Operator: L++ Canvas')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
