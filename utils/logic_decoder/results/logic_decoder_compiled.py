"""
L++ Compiled Operator: Python Logic Decoder
Version: 1.0.0
Description: Decode Python files into L++ blueprints by analyzing AST, control flow, and import semantics

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

BLUEPRINT_ID = 'logic_decoder'
BLUEPRINT_NAME = 'Python Logic Decoder'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'Idle',  # Awaiting file path or source code
    'parsing': 'Parsing',  # Parsing Python source into AST
    'analyzing': 'Analyzing',  # Analyzing imports, functions, and control flow
    # Inferring states, transitions, gates from code patterns
    'inferring': 'Inferring Logic',
    'generating': 'Generating Blueprint',  # Assembling final L++ blueprint
    'complete': 'Complete',  # Blueprint generated successfully
    'error': 'Error',  # Decoding failed
}

GATES = {
    'hasFilePath': 'True',
    'hasSourceCode': 'True',
    'hasAst': 'True',
    'hasAnalysis': 'True',
    'hasInferences': 'True',
    'hasError': 'True',
}

DISPLAY_RULES = [
]

ACTIONS = {
    'loadFile': {
        'type': 'compute',
        'compute_unit': 'decoder:loadFile',
        'input_map': {'filePath': 'filePath'},
        'output_map': {'sourceCode': 'sourceCode', 'error': 'error'},
    },
    'parseAst': {
        'type': 'compute',
        'compute_unit': 'decoder:parseAst',
        'input_map': {'sourceCode': 'sourceCode'},
        'output_map': {'ast': 'ast', 'error': 'error'},
    },
    'analyzeImports': {
        'type': 'compute',
        'compute_unit': 'decoder:analyzeImports',
        'input_map': {'ast': 'ast'},
        'output_map': {'imports': 'imports'},
    },
    'analyzeFunctions': {
        'type': 'compute',
        'compute_unit': 'decoder:analyzeFunctions',
        'input_map': {'ast': 'ast', 'imports': 'imports'},
        'output_map': {'functions': 'functions', 'classes': 'classes'},
    },
    'analyzeControlFlow': {
        'type': 'compute',
        'compute_unit': 'decoder:analyzeControlFlow',
        'input_map': {'ast': 'ast', 'functions': 'functions'},
        'output_map': {'controlFlow': 'controlFlow'},
    },
    'inferStates': {
        'type': 'compute',
        'compute_unit': 'decoder:inferStates',
        'input_map': {'functions': 'functions', 'classes': 'classes', 'controlFlow': 'controlFlow', 'imports': 'imports'},
        'output_map': {'inferredStates': 'states'},
    },
    'inferTransitions': {
        'type': 'compute',
        'compute_unit': 'decoder:inferTransitions',
        'input_map': {'controlFlow': 'controlFlow', 'inferredStates': 'inferredStates', 'functions': 'functions'},
        'output_map': {'inferredTransitions': 'transitions', 'inferredGates': 'gates'},
    },
    'inferActions': {
        'type': 'compute',
        'compute_unit': 'decoder:inferActions',
        'input_map': {'functions': 'functions', 'imports': 'imports', 'controlFlow': 'controlFlow'},
        'output_map': {'inferredActions': 'actions'},
    },
    'generateBlueprint': {
        'type': 'compute',
        'compute_unit': 'decoder:generateBlueprint',
        'input_map': {'filePath': 'filePath', 'inferredStates': 'inferredStates', 'inferredTransitions': 'inferredTransitions', 'inferredGates': 'inferredGates', 'inferredActions': 'inferredActions', 'imports': 'imports'},
        'output_map': {'blueprint': 'blueprint', 'blueprintJson': 'json', 'analysisReport': 'report'},
    },
    'setError': {
        'type': 'set',
        'target': 'error',
        'value_from': 'event.payload.message',
    },
    'clearError': {
        'type': 'set',
        'target': 'error',
    },
    'clearState': {
        'type': 'compute',
        'compute_unit': 'decoder:clearState',
        'output_map': {'ast': 'ast', 'imports': 'imports', 'functions': 'functions', 'classes': 'classes', 'controlFlow': 'controlFlow', 'inferredStates': 'inferredStates', 'inferredTransitions': 'inferredTransitions', 'inferredActions': 'inferredActions', 'inferredGates': 'inferredGates', 'blueprint': 'blueprint', 'blueprintJson': 'blueprintJson', 'analysisReport': 'analysisReport', 'error': 'error'},
    },
}

TRANSITIONS = [
    {
        'id': 't1_load',
        'from': 'idle',
        'to': 'parsing',
        'on_event': 'DECODE',
        'gates': [],
        'actions': ['loadFile'],
    },
    {
        'id': 't2_parse',
        'from': 'parsing',
        'to': 'analyzing',
        'on_event': 'AUTO',
        'gates': [],
        'actions': ['parseAst'],
    },
    {
        'id': 't3_analyze',
        'from': 'analyzing',
        'to': 'inferring',
        'on_event': 'AUTO',
        'gates': [],
        'actions': ['analyzeImports', 'analyzeFunctions', 'analyzeControlFlow'],
    },
    {
        'id': 't4_infer',
        'from': 'inferring',
        'to': 'generating',
        'on_event': 'AUTO',
        'gates': [],
        'actions': ['inferStates', 'inferTransitions', 'inferActions'],
    },
    {
        'id': 't5_generate',
        'from': 'generating',
        'to': 'complete',
        'on_event': 'AUTO',
        'gates': [],
        'actions': ['generateBlueprint'],
    },
    {
        'id': 't6_error_parse',
        'from': 'parsing',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['setError'],
    },
    {
        'id': 't7_error_analyze',
        'from': 'analyzing',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['setError'],
    },
    {
        'id': 't8_error_infer',
        'from': 'inferring',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['setError'],
    },
    {
        'id': 't9_reset',
        'from': 'complete',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clearState'],
    },
    {
        'id': 't10_error_reset',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clearError', 'clearState'],
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
    Compiled L++ Operator: Python Logic Decoder
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'filePath': None, 'sourceCode': None, 'ast': None, 'imports': None, 'functions': None, 'classes': None, 'controlFlow': None,
                        'inferredStates': None, 'inferredTransitions': None, 'inferredActions': None, 'inferredGates': None, 'blueprint': None, 'blueprintJson': None, 'analysisReport': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'filePath': None, 'sourceCode': None, 'ast': None, 'imports': None, 'functions': None, 'classes': None, 'controlFlow': None,
                        'inferredStates': None, 'inferredTransitions': None, 'inferredActions': None, 'inferredGates': None, 'blueprint': None, 'blueprintJson': None, 'analysisReport': None, 'error': None}
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
    print('L++ Compiled Operator: Python Logic Decoder')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
