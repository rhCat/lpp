"""
L++ Compiled Operator: L++ Test Case Generator
Version: 1.0.0
Description: Auto-generates test cases from L++ blueprints for comprehensive testing

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

BLUEPRINT_ID = 'test_generator'
BLUEPRINT_NAME = 'L++ Test Case Generator'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, ready to analyze
    'analyzing': 'analyzing',  # Analyzing blueprint structure
    'generating': 'generating',  # Generating test cases
    'complete': 'complete',  # Tests generated, ready to export
    'exporting': 'exporting',  # Exporting tests to file
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_graph': 'graph is not None',
    'has_paths': 'paths is not None and len(paths) > 0',
    'has_tests': 'all_tests is not None and len(all_tests) > 0',
    'has_path_tests': 'path_tests is not None',
    'has_gate_analysis': 'gate_analysis is not None',
    'format_is_json': "output_format == 'json'",
    'format_is_pytest': "output_format == 'pytest'",
    'has_output': 'formatted_output is not None',
}

DISPLAY_RULES = [
    {'gate': 'has_tests', 'template': 'Tests ready: {all_tests|len} tests generated'},
    {'gate': 'has_blueprint', 'template': 'Loaded: {blueprint.name}'},
    {'template': 'L++ Test Generator'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'testgen:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'path', 'error': 'error'},
    },
    'build_graph': {
        'type': 'compute',
        'compute_unit': 'testgen:build_graph',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'graph': 'graph'},
    },
    'analyze_paths': {
        'type': 'compute',
        'compute_unit': 'testgen:analyze_paths',
        'input_map': {'blueprint': 'blueprint', 'graph': 'graph'},
        'output_map': {'paths': 'paths'},
    },
    'analyze_gates': {
        'type': 'compute',
        'compute_unit': 'testgen:analyze_gates',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'gate_analysis': 'analysis'},
    },
    'generate_path_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:generate_path_tests',
        'input_map': {'blueprint': 'blueprint', 'paths': 'paths'},
        'output_map': {'path_tests': 'tests'},
    },
    'generate_state_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:generate_state_tests',
        'input_map': {'blueprint': 'blueprint', 'paths': 'paths'},
        'output_map': {'state_tests': 'tests'},
    },
    'generate_gate_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:generate_gate_tests',
        'input_map': {'blueprint': 'blueprint', 'gate_analysis': 'gate_analysis'},
        'output_map': {'gate_tests': 'tests'},
    },
    'generate_negative_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:generate_negative_tests',
        'input_map': {'blueprint': 'blueprint', 'graph': 'graph'},
        'output_map': {'negative_tests': 'tests'},
    },
    'generate_property_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:generate_property_tests',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'property_tests': 'tests'},
    },
    'combine_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:combine_tests',
        'input_map': {'blueprint': 'blueprint', 'path_tests': 'path_tests', 'state_tests': 'state_tests', 'gate_tests': 'gate_tests', 'negative_tests': 'negative_tests', 'property_tests': 'property_tests'},
        'output_map': {'all_tests': 'tests', 'coverage_report': 'coverage'},
    },
    'set_format_json': {
        'type': 'set',
        'target': 'output_format',
        'value': 'json',
    },
    'set_format_pytest': {
        'type': 'set',
        'target': 'output_format',
        'value': 'pytest',
    },
    'format_as_json': {
        'type': 'compute',
        'compute_unit': 'testgen:format_json',
        'input_map': {'blueprint': 'blueprint', 'tests': 'all_tests'},
        'output_map': {'formatted_output': 'output'},
    },
    'format_as_pytest': {
        'type': 'compute',
        'compute_unit': 'testgen:format_pytest',
        'input_map': {'blueprint': 'blueprint', 'tests': 'all_tests'},
        'output_map': {'formatted_output': 'output'},
    },
    'export_tests': {
        'type': 'compute',
        'compute_unit': 'testgen:export_tests',
        'input_map': {'content': 'formatted_output', 'path': 'event.payload.path', 'format': 'output_format'},
        'output_map': {'output_path': 'path'},
    },
    'clear_state': {
        'type': 'compute',
        'compute_unit': 'testgen:clear_state',
        'output_map': {'blueprint': 'blueprint', 'graph': 'graph', 'paths': 'paths', 'gate_analysis': 'gate_analysis', 'path_tests': 'path_tests', 'state_tests': 'state_tests', 'gate_tests': 'gate_tests', 'negative_tests': 'negative_tests', 'property_tests': 'property_tests', 'all_tests': 'all_tests', 'formatted_output': 'formatted_output', 'error': 'error'},
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
        'id': 't_load',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': ['no_blueprint'],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_reload',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['clear_state', 'load_blueprint'],
    },
    {
        'id': 't_reload_from_complete',
        'from': 'complete',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['clear_state', 'load_blueprint'],
    },
    {
        'id': 't_analyze',
        'from': 'loaded',
        'to': 'analyzing',
        'on_event': 'ANALYZE',
        'gates': ['has_blueprint'],
        'actions': ['build_graph', 'analyze_paths', 'analyze_gates'],
    },
    {
        'id': 't_generate_all',
        'from': 'analyzing',
        'to': 'generating',
        'on_event': 'GENERATE',
        'gates': ['has_paths'],
        'actions': ['generate_path_tests', 'generate_state_tests', 'generate_gate_tests', 'generate_negative_tests', 'generate_property_tests'],
    },
    {
        'id': 't_generate_from_loaded',
        'from': 'loaded',
        'to': 'generating',
        'on_event': 'GENERATE_ALL',
        'gates': ['has_blueprint'],
        'actions': ['build_graph', 'analyze_paths', 'analyze_gates', 'generate_path_tests', 'generate_state_tests', 'generate_gate_tests', 'generate_negative_tests', 'generate_property_tests'],
    },
    {
        'id': 't_combine',
        'from': 'generating',
        'to': 'complete',
        'on_event': 'COMBINE',
        'gates': ['has_path_tests'],
        'actions': ['combine_tests'],
    },
    {
        'id': 't_auto_combine',
        'from': 'generating',
        'to': 'complete',
        'on_event': 'AUTO',
        'gates': ['has_path_tests'],
        'actions': ['combine_tests'],
    },
    {
        'id': 't_format_json',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'FORMAT_JSON',
        'gates': ['has_tests'],
        'actions': ['set_format_json', 'format_as_json'],
    },
    {
        'id': 't_format_pytest',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'FORMAT_PYTEST',
        'gates': ['has_tests'],
        'actions': ['set_format_pytest', 'format_as_pytest'],
    },
    {
        'id': 't_export',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'EXPORT',
        'gates': ['has_output'],
        'actions': ['export_tests'],
    },
    {
        'id': 't_view_coverage',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'COVERAGE',
        'gates': ['has_tests'],
        'actions': [],
    },
    {
        'id': 't_reset',
        'from': 'complete',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_state'],
    },
    {
        'id': 't_reset_from_error',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_error', 'clear_state'],
    },
    {
        'id': 't_error_load',
        'from': 'idle',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_error_analyze',
        'from': 'analyzing',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_error_generate',
        'from': 'generating',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_back_to_loaded',
        'from': 'analyzing',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_back_from_complete',
        'from': 'complete',
        'to': 'loaded',
        'on_event': 'BACK',
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
    Compiled L++ Operator: L++ Test Case Generator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'graph': None, 'paths': None, 'gate_analysis': None, 'path_tests': None, 'state_tests': None, 'gate_tests': None,
                        'negative_tests': None, 'property_tests': None, 'all_tests': None, 'output_format': None, 'output_path': None, 'formatted_output': None, 'coverage_report': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'graph': None, 'paths': None, 'gate_analysis': None, 'path_tests': None, 'state_tests': None, 'gate_tests': None,
                        'negative_tests': None, 'property_tests': None, 'all_tests': None, 'output_format': None, 'output_path': None, 'formatted_output': None, 'coverage_report': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Test Case Generator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
