"""
L++ Compiled Operator: L++ Orchestrator
Version: 1.0.0
Description: Orchestrates blueprint execution using the four atomic operations

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

BLUEPRINT_ID = 'lpp_orchestrator'
BLUEPRINT_NAME = 'L++ Orchestrator'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = {'complete', 'error'}

STATES = {
    'idle': 'Idle',  # Waiting for event dispatch
    'finding_transition': 'Finding Transition',  # Searching for matching transition
    'evaluating_gates': 'Evaluating Gates',  # Checking gate conditions
    'executing_actions': 'Executing Actions',  # Running transition actions
    'transitioning': 'Transitioning',  # Performing state transition
    'complete': 'Complete',  # Event processed successfully
    'error': 'Error',  # Processing failed with error
}

GATES = {
    'g_has_transition': 'transition is not None',
    'g_not_terminal': 'current_state not in terminal_states',
}

DISPLAY_RULES = [
]

ACTIONS = {
    'a_find_transition': {
        'type': 'compute',
        'compute_unit': 'impl:_find_transition',
    },
    'a_evaluate_gate': {
        'type': 'compute',
        'compute_unit': 'impl:atom_EVALUATE',
    },
    'a_mutate_context': {
        'type': 'compute',
        'compute_unit': 'impl:atom_MUTATE',
    },
    'a_dispatch_compute': {
        'type': 'compute',
        'compute_unit': 'impl:atom_DISPATCH',
    },
    'a_transition': {
        'type': 'compute',
        'compute_unit': 'impl:atom_TRANSITION',
    },
    'a_append_trace': {
        'type': 'compute',
        'compute_unit': 'impl:traces.append',
    },
}

TRANSITIONS = [
    {
        'id': 't_dispatch',
        'from': 'idle',
        'to': 'finding_transition',
        'on_event': 'DISPATCH_EVENT',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_found',
        'from': 'finding_transition',
        'to': 'evaluating_gates',
        'on_event': 'TRANSITION_FOUND',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_gates_pass',
        'from': 'evaluating_gates',
        'to': 'executing_actions',
        'on_event': 'GATES_PASSED',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_actions_done',
        'from': 'executing_actions',
        'to': 'transitioning',
        'on_event': 'ACTIONS_DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_transition_done',
        'from': 'transitioning',
        'to': 'complete',
        'on_event': 'TRANSITION_DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_no_transition',
        'from': 'finding_transition',
        'to': 'error',
        'on_event': 'NO_TRANSITION',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_gates_fail',
        'from': 'evaluating_gates',
        'to': 'error',
        'on_event': 'GATES_FAILED',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_action_error',
        'from': 'executing_actions',
        'to': 'error',
        'on_event': 'ACTION_ERROR',
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
    Compiled L++ Operator: L++ Orchestrator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'error': None, 'result': None, 'current_state': None, 'event': None, 'traces': None}
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
                if not atom_EVALUATE(expr, scope):
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
                self.context = atom_MUTATE(self.context, target, value)
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
                    result = atom_DISPATCH(
                        sys_id, op_id, inp, self.compute_registry
                    )
                    for ctx_path, res_key in action.get('output_map', {}).items():
                        if res_key in result:
                            self.context = atom_MUTATE(
                                self.context, ctx_path, result[res_key]
                            )
                    scope.update(self.context)  # Sync scope for chained actions

        # TRANSITION
        new_state, trace = atom_TRANSITION(current, trans['to'])
        self.context = atom_MUTATE(self.context, '_state', new_state)
        self.traces.append(trace)

        return True, new_state, None

    def get(self, path: str):
        """Get a value from context by path."""
        return _resolve_path(path, self.context)

    def set(self, path: str, value):
        """Set a value in context by path."""
        self.context = atom_MUTATE(self.context, path, value)

    def display(self) -> str:
        """Evaluate display rules and return formatted string."""
        for rule in DISPLAY_RULES:
            gate = rule.get('gate')
            if gate:
                expr = GATES.get(gate, 'False')
                if not atom_EVALUATE(expr, self.context):
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
        self.context = {'_state': ENTRY_STATE, 'error': None, 'result': None, 'current_state': None, 'event': None, 'traces': None}
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
    print('L++ Compiled Operator: L++ Orchestrator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
