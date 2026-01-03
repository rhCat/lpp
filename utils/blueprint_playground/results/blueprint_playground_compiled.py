"""
L++ Compiled Operator: L++ Blueprint Playground
Version: 1.0.0
Description: Interactive web-based environment for editing and testing L++ blueprints

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

BLUEPRINT_ID = 'blueprint_playground'
BLUEPRINT_NAME = 'L++ Blueprint Playground'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'editing': 'editing',  # Blueprint loaded and being edited
    'validating': 'validating',  # Validating blueprint JSON/structure
    'simulating': 'simulating',  # Running interactive simulation
    'serving': 'serving',  # Web server is running
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint_json is not None and len(blueprint_json) > 0',
    'no_blueprint': 'blueprint_json is None or len(blueprint_json) == 0',
    'is_valid_json': 'is_valid_json == True',
    'is_invalid_json': 'is_valid_json == False',
    'is_valid_blueprint': 'is_valid_blueprint == True',
    'has_simulation': 'sim_state is not None',
    'no_simulation': 'sim_state is None',
    'has_error': 'error is not None',
    'no_error': 'error is None',
}

DISPLAY_RULES = [
    {'gate': 'has_error', 'template': 'ERROR: {error}'},
    {'gate': 'no_blueprint', 'template': 'No blueprint loaded. Use LOAD or paste JSON.'},
    {'gate': 'has_simulation', 'template': '[SIM] {blueprint_name} | State: {sim_state}'},
    {'gate': 'has_blueprint', 'template': '[EDIT] {blueprint_name} | Valid: {is_valid_blueprint}'},
    {'template': 'L++ Blueprint Playground'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'play:load_blueprint',
        'input_map': {'json_string': 'event.payload.json_string', 'file_path': 'event.payload.file_path'},
        'output_map': {'blueprint_json': 'blueprint_json', 'blueprint': 'blueprint', 'blueprint_name': 'blueprint_name', 'is_valid_json': 'is_valid_json', 'error': 'error'},
    },
    'validate_json': {
        'type': 'compute',
        'compute_unit': 'play:validate_json',
        'input_map': {'json_string': 'blueprint_json'},
        'output_map': {'is_valid_json': 'is_valid', 'validation_result': 'result', 'error': 'error'},
    },
    'validate_blueprint': {
        'type': 'compute',
        'compute_unit': 'play:validate_blueprint',
        'input_map': {'blueprint_json': 'blueprint_json'},
        'output_map': {'is_valid_blueprint': 'is_valid', 'validation_result': 'result', 'error': 'error'},
    },
    'format_blueprint': {
        'type': 'compute',
        'compute_unit': 'play:format_blueprint',
        'input_map': {'json_string': 'blueprint_json'},
        'output_map': {'blueprint_json': 'formatted', 'output': 'output'},
    },
    'generate_diagram': {
        'type': 'compute',
        'compute_unit': 'play:generate_diagram',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'mermaid_diagram': 'mermaid'},
    },
    'init_simulation': {
        'type': 'compute',
        'compute_unit': 'play:init_simulation',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'available_events': 'available_events', 'sim_trace': 'trace', 'output': 'output'},
    },
    'dispatch_event': {
        'type': 'compute',
        'compute_unit': 'play:dispatch_event',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'sim_trace': 'sim_trace', 'event_name': 'event.payload.event_name', 'event_payload': 'event.payload.event_payload'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'available_events': 'available_events', 'sim_trace': 'trace', 'output': 'output', 'error': 'error'},
    },
    'get_available_events': {
        'type': 'compute',
        'compute_unit': 'play:get_available_events',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context'},
        'output_map': {'available_events': 'events'},
    },
    'encode_share_url': {
        'type': 'compute',
        'compute_unit': 'play:encode_share_url',
        'input_map': {'blueprint_json': 'blueprint_json', 'base_url': 'event.payload.base_url'},
        'output_map': {'share_url': 'url', 'output': 'output'},
    },
    'decode_share_url': {
        'type': 'compute',
        'compute_unit': 'play:decode_share_url',
        'input_map': {'url': 'event.payload.url'},
        'output_map': {'blueprint_json': 'blueprint_json', 'blueprint': 'blueprint', 'blueprint_name': 'blueprint_name', 'is_valid_json': 'is_valid_json', 'output': 'output', 'error': 'error'},
    },
    'export_blueprint': {
        'type': 'compute',
        'compute_unit': 'play:export_blueprint',
        'input_map': {'blueprint_json': 'blueprint_json', 'file_path': 'event.payload.file_path'},
        'output_map': {'output': 'output', 'error': 'error'},
    },
    'update_blueprint': {
        'type': 'set',
        'target': 'blueprint_json',
        'value_from': 'event.payload.json_string',
    },
    'clear_blueprint': {
        'type': 'set',
        'target': 'blueprint_json',
    },
    'clear_simulation': {
        'type': 'set',
        'target': 'sim_state',
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
}

TRANSITIONS = [
    {
        'id': 't_load_from_idle',
        'from': 'idle',
        'to': 'editing',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'validate_blueprint', 'generate_diagram'],
    },
    {
        'id': 't_load_from_url',
        'from': 'idle',
        'to': 'editing',
        'on_event': 'LOAD_FROM_URL',
        'gates': [],
        'actions': ['decode_share_url', 'validate_blueprint', 'generate_diagram'],
    },
    {
        'id': 't_reload',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'validate_blueprint', 'generate_diagram'],
    },
    {
        'id': 't_update',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'UPDATE',
        'gates': [],
        'actions': ['update_blueprint', 'validate_json'],
    },
    {
        'id': 't_validate',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'VALIDATE',
        'gates': ['has_blueprint'],
        'actions': ['validate_json', 'validate_blueprint'],
    },
    {
        'id': 't_format',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'FORMAT',
        'gates': ['has_blueprint', 'is_valid_json'],
        'actions': ['format_blueprint', 'validate_blueprint', 'generate_diagram'],
    },
    {
        'id': 't_regenerate_diagram',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'REGENERATE_DIAGRAM',
        'gates': ['has_blueprint', 'is_valid_blueprint'],
        'actions': ['generate_diagram'],
    },
    {
        'id': 't_start_simulation',
        'from': 'editing',
        'to': 'simulating',
        'on_event': 'START_SIM',
        'gates': ['has_blueprint', 'is_valid_blueprint'],
        'actions': ['init_simulation'],
    },
    {
        'id': 't_dispatch_event',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'DISPATCH',
        'gates': ['has_simulation'],
        'actions': ['dispatch_event', 'get_available_events'],
    },
    {
        'id': 't_reset_simulation',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'RESET_SIM',
        'gates': [],
        'actions': ['init_simulation'],
    },
    {
        'id': 't_stop_simulation',
        'from': 'simulating',
        'to': 'editing',
        'on_event': 'STOP_SIM',
        'gates': [],
        'actions': ['clear_simulation'],
    },
    {
        'id': 't_share',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'SHARE',
        'gates': ['has_blueprint'],
        'actions': ['encode_share_url'],
    },
    {
        'id': 't_share_from_sim',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'SHARE',
        'gates': ['has_blueprint'],
        'actions': ['encode_share_url'],
    },
    {
        'id': 't_export',
        'from': 'editing',
        'to': 'editing',
        'on_event': 'EXPORT',
        'gates': ['has_blueprint'],
        'actions': ['export_blueprint'],
    },
    {
        'id': 't_export_from_sim',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'EXPORT',
        'gates': ['has_blueprint'],
        'actions': ['export_blueprint'],
    },
    {
        'id': 't_unload',
        'from': 'editing',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['clear_blueprint', 'clear_simulation'],
    },
    {
        'id': 't_unload_from_sim',
        'from': 'simulating',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['clear_blueprint', 'clear_simulation'],
    },
    {
        'id': 't_error_from_editing',
        'from': 'editing',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_error_from_simulating',
        'from': 'simulating',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_error', 'clear_blueprint', 'clear_simulation'],
    },
    {
        'id': 't_recover_to_editing',
        'from': 'error',
        'to': 'editing',
        'on_event': 'RETRY',
        'gates': ['has_blueprint'],
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
    Compiled L++ Operator: L++ Blueprint Playground
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint_json': None, 'blueprint': None, 'blueprint_name': None, 'validation_result': None, 'is_valid_json': None, 'is_valid_blueprint': None, 'mermaid_diagram': None, 'sim_state': None, 'sim_context': None, 'available_events': None, 'sim_trace': None, 'share_url': None, 'server_port': None, 'output': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint_json': None, 'blueprint': None, 'blueprint_name': None, 'validation_result': None, 'is_valid_json': None, 'is_valid_blueprint': None, 'mermaid_diagram': None, 'sim_state': None, 'sim_context': None, 'available_events': None, 'sim_trace': None, 'share_url': None, 'server_port': None, 'output': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Blueprint Playground')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
