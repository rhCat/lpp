"""
L++ Compiled Operator: L++ LLM Schema Assistant
Version: 1.0.0
Description: LLM-powered assistant for understanding and working with L++ blueprints. Automation agent building block.

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

BLUEPRINT_ID = 'llm_schema_assistant'
BLUEPRINT_NAME = 'L++ LLM Schema Assistant'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'init'
TERMINAL_STATES = set()

STATES = {
    'init': 'init',  # Initial state, checking API configuration
    'ready': 'ready',  # Configured and ready for queries
    'querying': 'querying',  # Sending query to LLM API
    'error': 'error',  # Error state - recoverable
}

GATES = {
    'has_api_key': 'api_key is not None',
    'no_api_key': 'api_key is None',
    'has_schema': 'schema_content is not None',
    'has_blueprint': 'blueprint is not None',
    'has_error': 'error is not None',
    'no_error': 'error is None',
}

DISPLAY_RULES = [
    {'gate': 'has_error', 'template': '❌ {error}'},
    {'gate': 'has_blueprint', 'template': '📋 {blueprint_path}'},
    {'gate': 'has_schema', 'template': '📖 Schema loaded'},
    {'template': '⚙️ Initializing...'},
]

ACTIONS = {
    'init_config': {
        'type': 'compute',
        'compute_unit': 'llm:init_config',
        'output_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'temperature': 'temperature', 'max_tokens': 'max_tokens'},
    },
    'load_schema': {
        'type': 'compute',
        'compute_unit': 'llm:load_schema',
        'output_map': {'schema_content': 'schema_content', 'error': 'error'},
    },
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'llm:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'error': 'error'},
    },
    'set_query': {
        'type': 'set',
        'target': 'last_query',
        'value_from': 'event.payload.query',
    },
    'query_llm': {
        'type': 'compute',
        'compute_unit': 'llm:query',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'temperature': 'temperature', 'max_tokens': 'max_tokens', 'schema_content': 'schema_content', 'blueprint': 'blueprint', 'conversation': 'conversation', 'query': 'last_query'},
        'output_map': {'last_response': 'response', 'conversation': 'conversation', 'error': 'error'},
    },
    'explain_blueprint': {
        'type': 'compute',
        'compute_unit': 'llm:explain_blueprint',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'temperature': 'temperature', 'max_tokens': 'max_tokens', 'schema_content': 'schema_content', 'blueprint': 'blueprint'},
        'output_map': {'last_response': 'response', 'conversation': 'conversation', 'error': 'error'},
    },
    'validate_blueprint': {
        'type': 'compute',
        'compute_unit': 'llm:validate_blueprint',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'schema_content': 'schema_content', 'blueprint': 'blueprint'},
        'output_map': {'last_response': 'response', 'error': 'error'},
    },
    'suggest_improvements': {
        'type': 'compute',
        'compute_unit': 'llm:suggest_improvements',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'schema_content': 'schema_content', 'blueprint': 'blueprint'},
        'output_map': {'last_response': 'response', 'error': 'error'},
    },
    'clear_conversation': {
        'type': 'set',
        'target': 'conversation',
        'value': [],
    },
    'clear_blueprint': {
        'type': 'set',
        'target': 'blueprint',
    },
    'clear_error': {
        'type': 'set',
        'target': 'error',
    },
}

TRANSITIONS = [
    {
        'id': 't_init_start',
        'from': 'init',
        'to': 'ready',
        'on_event': 'START',
        'gates': ['has_api_key'],
        'actions': ['load_schema'],
    },
    {
        'id': 't_init_no_key',
        'from': 'init',
        'to': 'error',
        'on_event': 'START',
        'gates': ['no_api_key'],
        'actions': [],
    },
    {
        'id': 't_configure',
        'from': '*',
        'to': 'init',
        'on_event': 'CONFIGURE',
        'gates': [],
        'actions': ['init_config'],
    },
    {
        'id': 't_set_key',
        'from': 'error',
        'to': 'init',
        'on_event': 'SET_KEY',
        'gates': [],
        'actions': ['clear_error'],
    },
    {
        'id': 't_load_blueprint',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'clear_conversation'],
    },
    {
        'id': 't_query',
        'from': 'ready',
        'to': 'querying',
        'on_event': 'QUERY',
        'gates': [],
        'actions': ['set_query', 'query_llm'],
    },
    {
        'id': 't_explain',
        'from': 'ready',
        'to': 'querying',
        'on_event': 'EXPLAIN',
        'gates': ['has_blueprint'],
        'actions': ['explain_blueprint'],
    },
    {
        'id': 't_validate',
        'from': 'ready',
        'to': 'querying',
        'on_event': 'VALIDATE',
        'gates': ['has_blueprint'],
        'actions': ['validate_blueprint'],
    },
    {
        'id': 't_suggest',
        'from': 'ready',
        'to': 'querying',
        'on_event': 'SUGGEST',
        'gates': ['has_blueprint'],
        'actions': ['suggest_improvements'],
    },
    {
        'id': 't_query_done',
        'from': 'querying',
        'to': 'ready',
        'on_event': 'DONE',
        'gates': ['no_error'],
        'actions': [],
    },
    {
        'id': 't_query_error',
        'from': 'querying',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_clear',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_conversation', 'clear_blueprint'],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'ready',
        'on_event': 'RETRY',
        'gates': ['has_api_key'],
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
    Compiled L++ Operator: L++ LLM Schema Assistant
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'api_key': None, 'api_base': None, 'model': None, 'schema_content': None, 'blueprint': None, 'blueprint_path': None, 'conversation': None, 'last_query': None, 'last_response': None, 'temperature': None, 'max_tokens': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'api_key': None, 'api_base': None, 'model': None, 'schema_content': None, 'blueprint': None, 'blueprint_path': None, 'conversation': None, 'last_query': None, 'last_response': None, 'temperature': None, 'max_tokens': None, 'error': None}
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
    print('L++ Compiled Operator: L++ LLM Schema Assistant')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
