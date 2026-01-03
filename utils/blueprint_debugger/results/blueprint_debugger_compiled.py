"""
L++ Compiled Operator: L++ Blueprint Debugger
Version: 1.0.0
Description: Step-through debugging for L++ blueprints with breakpoints, inspection, and time-travel debugging

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

BLUEPRINT_ID = 'lpp_blueprint_debugger'
BLUEPRINT_NAME = 'L++ Blueprint Debugger'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, ready to debug
    'debugging': 'debugging',  # Actively debugging, can step through execution
    'paused': 'paused',  # Paused at a breakpoint
    'inspecting': 'inspecting',  # Inspecting state or context
    'time_travel': 'time_travel',  # Navigating through history
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_history': 'history is not None and len(history) > 0',
    'can_step_back': 'history is not None and history_index > 0',
    'can_step_forward': 'history is not None and history_index < len(history) - 1',
    'has_breakpoints': 'breakpoints is not None and len(breakpoints) > 0',
    'has_watches': 'watches is not None and len(watches) > 0',
    'is_at_terminal': "blueprint is not None and debug_state in blueprint.get('terminal_states', [])",
    'is_paused_flag': 'is_paused == True',
    'is_not_paused': 'is_paused != True',
    'is_idle': "_state == 'idle'",
    'is_loaded': "_state == 'loaded'",
    'is_debugging': "_state == 'debugging'",
    'is_paused_state': "_state == 'paused'",
    'is_inspecting': "_state == 'inspecting'",
    'is_time_travel': "_state == 'time_travel'",
    'is_error': "_state == 'error'",
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprint loaded. Use LOAD command.'},
    {'gate': 'is_paused_state', 'template': '[PAUSED] {blueprint_name} @ {debug_state} (step {history_index})'},
    {'gate': 'is_debugging', 'template': '[DEBUG] {blueprint_name} @ {debug_state} (step {history_index})'},
    {'gate': 'is_inspecting', 'template': '[INSPECT] {blueprint_name} @ {debug_state}'},
    {'gate': 'is_time_travel', 'template': '[TIME-TRAVEL] {blueprint_name} @ step {history_index}'},
    {'gate': 'is_loaded', 'template': 'Loaded: {blueprint_name} - Ready to debug'},
    {'template': 'L++ Blueprint Debugger'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'debug:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'blueprint_name': 'blueprint_name', 'blueprint_id': 'blueprint_id', 'error': 'error'},
    },
    'init_debug_session': {
        'type': 'compute',
        'compute_unit': 'debug:init_debug_session',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'breakpoints': 'breakpoints', 'watches': 'watches', 'watch_values': 'watch_values', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'is_paused': 'is_paused', 'output': 'output'},
    },
    'reset_session': {
        'type': 'compute',
        'compute_unit': 'debug:reset_session',
        'input_map': {'blueprint': 'blueprint', 'breakpoints': 'breakpoints', 'watches': 'watches'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'is_paused': 'is_paused', 'output': 'output'},
    },
    'set_breakpoint': {
        'type': 'compute',
        'compute_unit': 'debug:set_breakpoint',
        'input_map': {'breakpoints': 'breakpoints', 'bp_type': 'event.payload.type', 'target': 'event.payload.target', 'condition': 'event.payload.condition'},
        'output_map': {'breakpoints': 'breakpoints', 'output': 'output'},
    },
    'remove_breakpoint': {
        'type': 'compute',
        'compute_unit': 'debug:remove_breakpoint',
        'input_map': {'breakpoints': 'breakpoints', 'bp_id': 'event.payload.bp_id'},
        'output_map': {'breakpoints': 'breakpoints', 'output': 'output'},
    },
    'list_breakpoints': {
        'type': 'compute',
        'compute_unit': 'debug:list_breakpoints',
        'input_map': {'breakpoints': 'breakpoints'},
        'output_map': {'output': 'output'},
    },
    'step': {
        'type': 'compute',
        'compute_unit': 'debug:step',
        'input_map': {'blueprint': 'blueprint', 'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'breakpoints': 'breakpoints', 'watches': 'watches', 'event_name': 'event.payload.event_name', 'event_payload': 'event.payload.payload'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'last_transition': 'last_transition', 'last_gate_results': 'last_gate_results', 'last_action_results': 'last_action_results', 'watch_values': 'watch_values', 'is_paused': 'is_paused', 'hit_breakpoint': 'hit_breakpoint', 'output': 'output', 'error': 'error'},
    },
    'step_over': {
        'type': 'compute',
        'compute_unit': 'debug:step_over',
        'input_map': {'blueprint': 'blueprint', 'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'breakpoints': 'breakpoints', 'watches': 'watches', 'event_name': 'event.payload.event_name', 'event_payload': 'event.payload.payload'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'last_transition': 'last_transition', 'watch_values': 'watch_values', 'is_paused': 'is_paused', 'hit_breakpoint': 'hit_breakpoint', 'output': 'output', 'error': 'error'},
    },
    'step_back': {
        'type': 'compute',
        'compute_unit': 'debug:step_back',
        'input_map': {'history': 'history', 'history_index': 'history_index', 'blueprint': 'blueprint', 'watches': 'watches'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'watch_values': 'watch_values', 'output': 'output'},
    },
    'run_to_breakpoint': {
        'type': 'compute',
        'compute_unit': 'debug:run_to_breakpoint',
        'input_map': {'blueprint': 'blueprint', 'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'breakpoints': 'breakpoints', 'watches': 'watches', 'max_steps': 'event.payload.max_steps'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'watch_values': 'watch_values', 'is_paused': 'is_paused', 'hit_breakpoint': 'hit_breakpoint', 'output': 'output', 'error': 'error'},
    },
    'continue_execution': {
        'type': 'compute',
        'compute_unit': 'debug:continue_execution',
        'input_map': {'blueprint': 'blueprint', 'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'breakpoints': 'breakpoints', 'watches': 'watches'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history': 'history', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'watch_values': 'watch_values', 'is_paused': 'is_paused', 'hit_breakpoint': 'hit_breakpoint', 'output': 'output', 'error': 'error'},
    },
    'pause_execution': {
        'type': 'set',
        'target': 'is_paused',
        'value': True,
    },
    'resume_execution': {
        'type': 'set',
        'target': 'is_paused',
        'value': False,
    },
    'inspect_state': {
        'type': 'compute',
        'compute_unit': 'debug:inspect_state',
        'input_map': {'blueprint': 'blueprint', 'debug_state': 'debug_state', 'available_transitions': 'available_transitions'},
        'output_map': {'output': 'output'},
    },
    'inspect_context': {
        'type': 'compute',
        'compute_unit': 'debug:inspect_context',
        'input_map': {'debug_context': 'debug_context', 'key': 'event.payload.key'},
        'output_map': {'output': 'output'},
    },
    'evaluate_expression': {
        'type': 'compute',
        'compute_unit': 'debug:evaluate_expression',
        'input_map': {'debug_context': 'debug_context', 'expression': 'event.payload.expression'},
        'output_map': {'output': 'output'},
    },
    'add_watch': {
        'type': 'compute',
        'compute_unit': 'debug:add_watch',
        'input_map': {'watches': 'watches', 'expression': 'event.payload.expression', 'name': 'event.payload.name'},
        'output_map': {'watches': 'watches', 'output': 'output'},
    },
    'remove_watch': {
        'type': 'compute',
        'compute_unit': 'debug:remove_watch',
        'input_map': {'watches': 'watches', 'watch_id': 'event.payload.watch_id'},
        'output_map': {'watches': 'watches', 'output': 'output'},
    },
    'get_watches': {
        'type': 'compute',
        'compute_unit': 'debug:get_watches',
        'input_map': {'watches': 'watches', 'watch_values': 'watch_values', 'debug_context': 'debug_context'},
        'output_map': {'watch_values': 'watch_values', 'output': 'output'},
    },
    'get_history': {
        'type': 'compute',
        'compute_unit': 'debug:get_history',
        'input_map': {'history': 'history', 'history_index': 'history_index'},
        'output_map': {'output': 'output'},
    },
    'goto_step': {
        'type': 'compute',
        'compute_unit': 'debug:goto_step',
        'input_map': {'history': 'history', 'target_step': 'event.payload.step', 'blueprint': 'blueprint', 'watches': 'watches'},
        'output_map': {'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history_index': 'history_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'watch_values': 'watch_values', 'output': 'output'},
    },
    'compare_states': {
        'type': 'compute',
        'compute_unit': 'debug:compare_states',
        'input_map': {'history': 'history', 'step1': 'event.payload.step1', 'step2': 'event.payload.step2'},
        'output_map': {'output': 'output'},
    },
    'render_status': {
        'type': 'compute',
        'compute_unit': 'debug:render_status',
        'input_map': {'blueprint_name': 'blueprint_name', 'debug_state': 'debug_state', 'debug_context': 'debug_context', 'history_index': 'history_index', 'available_events': 'available_events', 'breakpoints': 'breakpoints', 'is_paused': 'is_paused', 'hit_breakpoint': 'hit_breakpoint'},
        'output_map': {'output': 'output'},
    },
    'set_error': {
        'type': 'set',
        'target': 'error',
        'value_from': 'event.payload.message',
    },
    'clear_error': {
        'type': 'set',
        'target': 'error',
    },
    'clear_hit_breakpoint': {
        'type': 'set',
        'target': 'hit_breakpoint',
    },
    'unload_blueprint': {
        'type': 'set',
        'target': 'blueprint',
    },
}

TRANSITIONS = [
    {
        'id': 't_load',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': ['no_blueprint'],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_load_error',
        'from': 'idle',
        'to': 'error',
        'on_event': 'LOAD_FAILED',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_reload',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_reload_from_debug',
        'from': 'debugging',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_start_debug',
        'from': 'loaded',
        'to': 'debugging',
        'on_event': 'START',
        'gates': ['has_blueprint'],
        'actions': ['init_debug_session', 'render_status'],
    },
    {
        'id': 't_set_bp_loaded',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'SET_BREAKPOINT',
        'gates': [],
        'actions': ['set_breakpoint'],
    },
    {
        'id': 't_set_bp_debug',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'SET_BREAKPOINT',
        'gates': [],
        'actions': ['set_breakpoint'],
    },
    {
        'id': 't_set_bp_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'SET_BREAKPOINT',
        'gates': [],
        'actions': ['set_breakpoint'],
    },
    {
        'id': 't_remove_bp_debug',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'REMOVE_BREAKPOINT',
        'gates': [],
        'actions': ['remove_breakpoint'],
    },
    {
        'id': 't_remove_bp_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'REMOVE_BREAKPOINT',
        'gates': [],
        'actions': ['remove_breakpoint'],
    },
    {
        'id': 't_list_bp_debug',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'LIST_BREAKPOINTS',
        'gates': [],
        'actions': ['list_breakpoints'],
    },
    {
        'id': 't_list_bp_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'LIST_BREAKPOINTS',
        'gates': [],
        'actions': ['list_breakpoints'],
    },
    {
        'id': 't_step',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'STEP',
        'gates': ['is_not_paused'],
        'actions': ['step'],
    },
    {
        'id': 't_step_to_paused',
        'from': 'debugging',
        'to': 'paused',
        'on_event': 'STEP_HIT_BP',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_step_over',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'STEP_OVER',
        'gates': ['is_not_paused'],
        'actions': ['step_over'],
    },
    {
        'id': 't_step_back',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'STEP_BACK',
        'gates': ['can_step_back'],
        'actions': ['step_back'],
    },
    {
        'id': 't_step_back_paused',
        'from': 'paused',
        'to': 'debugging',
        'on_event': 'STEP_BACK',
        'gates': ['can_step_back'],
        'actions': ['step_back', 'clear_hit_breakpoint'],
    },
    {
        'id': 't_run',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'RUN',
        'gates': [],
        'actions': ['run_to_breakpoint'],
    },
    {
        'id': 't_run_hit_bp',
        'from': 'debugging',
        'to': 'paused',
        'on_event': 'RUN_HIT_BP',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_continue',
        'from': 'paused',
        'to': 'debugging',
        'on_event': 'CONTINUE',
        'gates': [],
        'actions': ['clear_hit_breakpoint', 'resume_execution'],
    },
    {
        'id': 't_continue_run',
        'from': 'paused',
        'to': 'debugging',
        'on_event': 'RUN',
        'gates': [],
        'actions': ['clear_hit_breakpoint', 'continue_execution'],
    },
    {
        'id': 't_pause',
        'from': 'debugging',
        'to': 'paused',
        'on_event': 'PAUSE',
        'gates': [],
        'actions': ['pause_execution'],
    },
    {
        'id': 't_stop',
        'from': 'debugging',
        'to': 'loaded',
        'on_event': 'STOP',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_stop_paused',
        'from': 'paused',
        'to': 'loaded',
        'on_event': 'STOP',
        'gates': [],
        'actions': ['clear_hit_breakpoint'],
    },
    {
        'id': 't_inspect_state',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'INSPECT_STATE',
        'gates': [],
        'actions': ['inspect_state'],
    },
    {
        'id': 't_inspect_state_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'INSPECT_STATE',
        'gates': [],
        'actions': ['inspect_state'],
    },
    {
        'id': 't_inspect_context',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'INSPECT_CONTEXT',
        'gates': [],
        'actions': ['inspect_context'],
    },
    {
        'id': 't_inspect_context_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'INSPECT_CONTEXT',
        'gates': [],
        'actions': ['inspect_context'],
    },
    {
        'id': 't_eval',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'EVAL',
        'gates': [],
        'actions': ['evaluate_expression'],
    },
    {
        'id': 't_eval_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'EVAL',
        'gates': [],
        'actions': ['evaluate_expression'],
    },
    {
        'id': 't_add_watch',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'ADD_WATCH',
        'gates': [],
        'actions': ['add_watch'],
    },
    {
        'id': 't_add_watch_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'ADD_WATCH',
        'gates': [],
        'actions': ['add_watch'],
    },
    {
        'id': 't_remove_watch',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'REMOVE_WATCH',
        'gates': [],
        'actions': ['remove_watch'],
    },
    {
        'id': 't_get_watches',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'GET_WATCHES',
        'gates': [],
        'actions': ['get_watches'],
    },
    {
        'id': 't_get_watches_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'GET_WATCHES',
        'gates': [],
        'actions': ['get_watches'],
    },
    {
        'id': 't_history',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'HISTORY',
        'gates': [],
        'actions': ['get_history'],
    },
    {
        'id': 't_history_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'HISTORY',
        'gates': [],
        'actions': ['get_history'],
    },
    {
        'id': 't_goto_step',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'GOTO',
        'gates': ['has_history'],
        'actions': ['goto_step'],
    },
    {
        'id': 't_goto_step_paused',
        'from': 'paused',
        'to': 'debugging',
        'on_event': 'GOTO',
        'gates': ['has_history'],
        'actions': ['goto_step', 'clear_hit_breakpoint'],
    },
    {
        'id': 't_compare',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'COMPARE',
        'gates': [],
        'actions': ['compare_states'],
    },
    {
        'id': 't_compare_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'COMPARE',
        'gates': [],
        'actions': ['compare_states'],
    },
    {
        'id': 't_reset',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['reset_session'],
    },
    {
        'id': 't_reset_paused',
        'from': 'paused',
        'to': 'debugging',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['reset_session', 'clear_hit_breakpoint'],
    },
    {
        'id': 't_status',
        'from': 'debugging',
        'to': 'debugging',
        'on_event': 'STATUS',
        'gates': [],
        'actions': ['render_status'],
    },
    {
        'id': 't_status_paused',
        'from': 'paused',
        'to': 'paused',
        'on_event': 'STATUS',
        'gates': [],
        'actions': ['render_status'],
    },
    {
        'id': 't_unload',
        'from': 'loaded',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint'],
    },
    {
        'id': 't_unload_debug',
        'from': 'debugging',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint'],
    },
    {
        'id': 't_unload_paused',
        'from': 'paused',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint', 'clear_hit_breakpoint'],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_error'],
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
    Compiled L++ Operator: L++ Blueprint Debugger
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'blueprint_id': None, 'debug_state': None, 'debug_context': None, 'breakpoints': None, 'watches': None, 'watch_values': None, 'history': None, 'history_index': None, 'available_events': None, 'available_transitions': None, 'last_transition': None, 'last_gate_results': None, 'last_action_results': None, 'is_paused': None, 'hit_breakpoint': None, 'output': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'blueprint_id': None, 'debug_state': None, 'debug_context': None, 'breakpoints': None, 'watches': None, 'watch_values': None, 'history': None, 'history_index': None, 'available_events': None, 'available_transitions': None, 'last_transition': None, 'last_gate_results': None, 'last_action_results': None, 'is_paused': None, 'hit_breakpoint': None, 'output': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Blueprint Debugger')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
