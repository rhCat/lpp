"""
L++ Compiled Operator: Policy Generator
Version: 1.0.0
Description: Generate L++ policies from decoded blueprints or source repositories with provenance tracking

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

BLUEPRINT_ID = 'policy_generator'
BLUEPRINT_NAME = 'Policy Generator'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = {'error', 'complete'}

STATES = {
    'idle': 'idle',  # Awaiting source input
    'analyzing': 'analyzing',  # Running decoders on source
    'extracting_states': 'extracting_states',  # Identifying state patterns
    'extracting_slots': 'extracting_slots',  # Finding customization points
    'extracting_terminals': 'extracting_terminals',  # Identifying terminal states and contracts
    'composing': 'composing',  # Building policy structure
    'generating_tla': 'generating_tla',  # Creating TLA+ specification
    'validating': 'validating',  # Verifying policy correctness
    'writing': 'writing',  # Saving policy to disk
    'complete': 'complete',  # Policy generation complete
    'error': 'error',  # Error occurred during generation
}

GATES = {
    'has_source': 'source_path is not None',
    'has_states': 'extracted_states is not None',
    'has_terminals': 'extracted_terminals is not None',
    'policy_valid': 'policy is not None',
}

DISPLAY_RULES = [
]

ACTIONS = {
    'analyze_source': {
        'type': 'compute',
        'compute_unit': 'policy_gen:analyzeSource',
        'input_map': {'source_path': 'source_path', 'source_repo': 'source_repo', 'source_type': 'source_type'},
        'output_map': {'decoded_blueprints': 'decoded_blueprints', 'function_analysis': 'function_analysis', 'provenance': 'provenance', 'source_type': 'source_type'},
    },
    'extract_states': {
        'type': 'compute',
        'compute_unit': 'policy_gen:extractStates',
        'input_map': {'decoded_blueprints': 'decoded_blueprints'},
        'output_map': {'extracted_states': 'extracted_states', 'state_definitions': 'state_definitions', 'state_sources': 'state_sources', 'entry_state': 'entry_state'},
    },
    'extract_slots': {
        'type': 'compute',
        'compute_unit': 'policy_gen:extractSlots',
        'input_map': {'decoded_blueprints': 'decoded_blueprints', 'function_analysis': 'function_analysis'},
        'output_map': {'extracted_slots': 'extracted_slots'},
    },
    'extract_terminals': {
        'type': 'compute',
        'compute_unit': 'policy_gen:extractTerminals',
        'input_map': {'decoded_blueprints': 'decoded_blueprints', 'extracted_states': 'extracted_states'},
        'output_map': {'extracted_terminals': 'extracted_terminals'},
    },
    'compose_policy': {
        'type': 'compute',
        'compute_unit': 'policy_gen:composePolicy',
        'input_map': {'policy_name': 'policy_name', 'state_definitions': 'state_definitions', 'entry_state': 'entry_state', 'extracted_terminals': 'extracted_terminals', 'extracted_slots': 'extracted_slots', 'provenance': 'provenance'},
        'output_map': {'policy': 'policy'},
    },
    'generate_tla': {
        'type': 'compute',
        'compute_unit': 'policy_gen:generateTla',
        'input_map': {'policy': 'policy'},
        'output_map': {'tla_spec': 'tla_spec'},
    },
    'validate_policy': {
        'type': 'compute',
        'compute_unit': 'policy_gen:validatePolicy',
        'input_map': {'policy': 'policy'},
        'output_map': {'validation_errors': 'validation_errors', 'valid': 'valid'},
    },
    'write_policy': {
        'type': 'compute',
        'compute_unit': 'policy_gen:writePolicy',
        'input_map': {'policy': 'policy', 'tla_spec': 'tla_spec', 'output_path': 'output_path'},
        'output_map': {'output_path': 'output_path', 'tla_path': 'tla_path'},
    },
}

TRANSITIONS = [
    {
        'id': 't_start',
        'from': 'idle',
        'to': 'analyzing',
        'on_event': 'GENERATE',
        'gates': ['has_source'],
        'actions': ['analyze_source'],
    },
    {
        'id': 't_analyzed',
        'from': 'analyzing',
        'to': 'extracting_states',
        'on_event': 'ANALYZED',
        'gates': [],
        'actions': ['extract_states'],
    },
    {
        'id': 't_states_done',
        'from': 'extracting_states',
        'to': 'extracting_slots',
        'on_event': 'STATES_EXTRACTED',
        'gates': ['has_states'],
        'actions': ['extract_slots'],
    },
    {
        'id': 't_slots_done',
        'from': 'extracting_slots',
        'to': 'extracting_terminals',
        'on_event': 'SLOTS_EXTRACTED',
        'gates': [],
        'actions': ['extract_terminals'],
    },
    {
        'id': 't_terminals_done',
        'from': 'extracting_terminals',
        'to': 'composing',
        'on_event': 'TERMINALS_EXTRACTED',
        'gates': ['has_terminals'],
        'actions': ['compose_policy'],
    },
    {
        'id': 't_composed',
        'from': 'composing',
        'to': 'generating_tla',
        'on_event': 'COMPOSED',
        'gates': [],
        'actions': ['generate_tla'],
    },
    {
        'id': 't_tla_done',
        'from': 'generating_tla',
        'to': 'validating',
        'on_event': 'TLA_GENERATED',
        'gates': [],
        'actions': ['validate_policy'],
    },
    {
        'id': 't_validated',
        'from': 'validating',
        'to': 'writing',
        'on_event': 'VALIDATED',
        'gates': ['policy_valid'],
        'actions': ['write_policy'],
    },
    {
        'id': 't_written',
        'from': 'writing',
        'to': 'complete',
        'on_event': 'WRITTEN',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_error',
        'from': '*',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': [],
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
    Compiled L++ Operator: Policy Generator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'source_path': None, 'source_type': None, 'source_repo': None, 'policy_name': None, 'decoded_blueprints': None, 'function_analysis': None, 'extracted_states': None, 'extracted_slots': None, 'extracted_terminals': None, 'provenance': None, 'policy': None, 'tla_spec': None, 'output_path': None, 'state_definitions': None, 'state_sources': None, 'entry_state': None, 'validation_errors': None, 'valid': None, 'tla_path': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'source_path': None, 'source_type': None, 'source_repo': None, 'policy_name': None, 'decoded_blueprints': None, 'function_analysis': None, 'extracted_states': None, 'extracted_slots': None, 'extracted_terminals': None, 'provenance': None, 'policy': None, 'tla_spec': None, 'output_path': None, 'state_definitions': None, 'state_sources': None, 'entry_state': None, 'validation_errors': None, 'valid': None, 'tla_path': None, 'error': None}
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
    print('L++ Compiled Operator: Policy Generator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
