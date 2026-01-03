"""
L++ Compiled Operator: Legacy Code State Machine Extractor
Version: 1.0.0
Description: Extract state machine patterns from legacy Python code and convert to L++ blueprints

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

BLUEPRINT_ID = 'legacy_extractor'
BLUEPRINT_NAME = 'Legacy Code State Machine Extractor'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # Awaiting source file or code input
    'loading': 'loading',  # Loading source file from disk
    'parsing': 'parsing',  # Parsing Python source into AST
    'detecting': 'detecting',  # Detecting state machine patterns in code
    'extracting_states': 'extracting_states',  # Extracting state definitions from code
    'extracting_transitions': 'extracting_transitions',  # Extracting state transitions from methods
    'extracting_gates': 'extracting_gates',  # Extracting gate conditions from if statements
    'extracting_actions': 'extracting_actions',  # Extracting actions from side effects
    'analyzing_events': 'analyzing_events',  # Analyzing event handler patterns
    'inferring_entry': 'inferring_entry',  # Inferring entry and terminal states
    'generating': 'generating',  # Generating L++ blueprint
    'mapping': 'mapping',  # Generating source-to-blueprint mapping
    'complete': 'complete',  # Extraction complete, blueprint ready
    'error': 'error',  # Extraction failed
}

GATES = {
    'hasFilePath': 'filePath is not None and len(filePath) > 0',
    'hasSourceCode': 'sourceCode is not None and len(sourceCode) > 0',
    'hasAst': 'ast is not None',
    'hasPatterns': 'patterns is not None',
    'hasStates': 'extractedStates is not None and len(extractedStates) > 0',
    'hasTransitions': 'extractedTransitions is not None',
    'hasGates': 'extractedGates is not None',
    'hasActions': 'extractedActions is not None',
    'hasEvents': 'extractedEvents is not None',
    'hasEntryState': 'entryState is not None',
    'hasBlueprint': 'blueprint is not None',
    'hasMapping': 'sourceMapping is not None',
    'hasError': 'error is not None and len(error) > 0',
    'noError': 'error is None or len(error) == 0',
}

DISPLAY_RULES = [
    {'gate': 'hasError', 'template': 'ERROR: {error}'},
    {'gate': 'hasBlueprint', 'template': 'Blueprint ready: {blueprint.id}'},
    {'template': 'Legacy Extractor [{analysisMode}]'},
]

ACTIONS = {
    'loadSource': {
        'type': 'compute',
        'compute_unit': 'extract:loadSource',
        'input_map': {'filePath': 'filePath'},
        'output_map': {'sourceCode': 'sourceCode', 'error': 'error'},
    },
    'parseAst': {
        'type': 'compute',
        'compute_unit': 'extract:parseAst',
        'input_map': {'sourceCode': 'sourceCode'},
        'output_map': {'ast': 'ast', 'error': 'error'},
    },
    'findStatePatterns': {
        'type': 'compute',
        'compute_unit': 'extract:findStatePatterns',
        'input_map': {'ast': 'ast', 'analysisMode': 'analysisMode'},
        'output_map': {'patterns': 'patterns'},
    },
    'extractStates': {
        'type': 'compute',
        'compute_unit': 'extract:extractStates',
        'input_map': {'ast': 'ast', 'patterns': 'patterns'},
        'output_map': {'extractedStates': 'states', 'uncertainties': 'uncertainties'},
    },
    'extractTransitions': {
        'type': 'compute',
        'compute_unit': 'extract:extractTransitions',
        'input_map': {'ast': 'ast', 'patterns': 'patterns', 'extractedStates': 'extractedStates'},
        'output_map': {'extractedTransitions': 'transitions', 'uncertainties': 'uncertainties'},
    },
    'extractGates': {
        'type': 'compute',
        'compute_unit': 'extract:extractGates',
        'input_map': {'ast': 'ast', 'patterns': 'patterns', 'extractedTransitions': 'extractedTransitions'},
        'output_map': {'extractedGates': 'gates', 'uncertainties': 'uncertainties'},
    },
    'extractActions': {
        'type': 'compute',
        'compute_unit': 'extract:extractActions',
        'input_map': {'ast': 'ast', 'patterns': 'patterns', 'extractedTransitions': 'extractedTransitions'},
        'output_map': {'extractedActions': 'actions', 'uncertainties': 'uncertainties'},
    },
    'analyzeEventHandlers': {
        'type': 'compute',
        'compute_unit': 'extract:analyzeEventHandlers',
        'input_map': {'ast': 'ast', 'patterns': 'patterns', 'extractedStates': 'extractedStates'},
        'output_map': {'extractedEvents': 'events', 'uncertainties': 'uncertainties'},
    },
    'inferEntryState': {
        'type': 'compute',
        'compute_unit': 'extract:inferEntryState',
        'input_map': {'ast': 'ast', 'patterns': 'patterns', 'extractedStates': 'extractedStates', 'extractedTransitions': 'extractedTransitions'},
        'output_map': {'entryState': 'entryState', 'terminalStates': 'terminalStates'},
    },
    'generateBlueprint': {
        'type': 'compute',
        'compute_unit': 'extract:generateBlueprint',
        'input_map': {'filePath': 'filePath', 'extractedStates': 'extractedStates', 'extractedTransitions': 'extractedTransitions', 'extractedGates': 'extractedGates', 'extractedActions': 'extractedActions', 'extractedEvents': 'extractedEvents', 'entryState': 'entryState', 'terminalStates': 'terminalStates'},
        'output_map': {'blueprint': 'blueprint', 'blueprintJson': 'blueprintJson'},
    },
    'generateMapping': {
        'type': 'compute',
        'compute_unit': 'extract:generateMapping',
        'input_map': {'filePath': 'filePath', 'extractedStates': 'extractedStates', 'extractedTransitions': 'extractedTransitions', 'extractedGates': 'extractedGates', 'extractedActions': 'extractedActions', 'blueprint': 'blueprint'},
        'output_map': {'sourceMapping': 'sourceMapping', 'extractionReport': 'report'},
    },
    'exportBlueprint': {
        'type': 'compute',
        'compute_unit': 'extract:exportBlueprint',
        'input_map': {'blueprintJson': 'blueprintJson', 'outputPath': 'event.payload.outputPath'},
        'output_map': {'error': 'error'},
    },
    'exportReport': {
        'type': 'compute',
        'compute_unit': 'extract:exportReport',
        'input_map': {'extractionReport': 'extractionReport', 'sourceMapping': 'sourceMapping', 'uncertainties': 'uncertainties', 'outputPath': 'event.payload.outputPath'},
        'output_map': {'error': 'error'},
    },
    'setMode': {
        'type': 'set',
        'target': 'analysisMode',
        'value_from': 'event.payload.mode',
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
        'compute_unit': 'extract:clearState',
        'output_map': {'sourceCode': 'sourceCode', 'ast': 'ast', 'patterns': 'patterns', 'extractedStates': 'extractedStates', 'extractedTransitions': 'extractedTransitions', 'extractedGates': 'extractedGates', 'extractedActions': 'extractedActions', 'extractedEvents': 'extractedEvents', 'entryState': 'entryState', 'terminalStates': 'terminalStates', 'blueprint': 'blueprint', 'blueprintJson': 'blueprintJson', 'sourceMapping': 'sourceMapping', 'uncertainties': 'uncertainties', 'extractionReport': 'extractionReport', 'error': 'error'},
    },
}

TRANSITIONS = [
    {
        'id': 't_set_mode',
        'from': 'idle',
        'to': 'idle',
        'on_event': 'SET_MODE',
        'gates': [],
        'actions': ['setMode'],
    },
    {
        'id': 't_start_extract',
        'from': 'idle',
        'to': 'loading',
        'on_event': 'EXTRACT',
        'gates': ['hasFilePath'],
        'actions': ['loadSource'],
    },
    {
        'id': 't_load_error',
        'from': 'loading',
        'to': 'error',
        'on_event': 'AUTO',
        'gates': ['hasError'],
        'actions': [],
    },
    {
        'id': 't_load_done',
        'from': 'loading',
        'to': 'parsing',
        'on_event': 'AUTO',
        'gates': ['hasSourceCode', 'noError'],
        'actions': ['parseAst'],
    },
    {
        'id': 't_parse_error',
        'from': 'parsing',
        'to': 'error',
        'on_event': 'AUTO',
        'gates': ['hasError'],
        'actions': [],
    },
    {
        'id': 't_parse_done',
        'from': 'parsing',
        'to': 'detecting',
        'on_event': 'AUTO',
        'gates': ['hasAst', 'noError'],
        'actions': ['findStatePatterns'],
    },
    {
        'id': 't_detect_done',
        'from': 'detecting',
        'to': 'extracting_states',
        'on_event': 'AUTO',
        'gates': ['hasPatterns'],
        'actions': ['extractStates'],
    },
    {
        'id': 't_states_done',
        'from': 'extracting_states',
        'to': 'extracting_transitions',
        'on_event': 'AUTO',
        'gates': ['hasStates'],
        'actions': ['extractTransitions'],
    },
    {
        'id': 't_transitions_done',
        'from': 'extracting_transitions',
        'to': 'extracting_gates',
        'on_event': 'AUTO',
        'gates': ['hasTransitions'],
        'actions': ['extractGates'],
    },
    {
        'id': 't_gates_done',
        'from': 'extracting_gates',
        'to': 'extracting_actions',
        'on_event': 'AUTO',
        'gates': ['hasGates'],
        'actions': ['extractActions'],
    },
    {
        'id': 't_actions_done',
        'from': 'extracting_actions',
        'to': 'analyzing_events',
        'on_event': 'AUTO',
        'gates': ['hasActions'],
        'actions': ['analyzeEventHandlers'],
    },
    {
        'id': 't_events_done',
        'from': 'analyzing_events',
        'to': 'inferring_entry',
        'on_event': 'AUTO',
        'gates': ['hasEvents'],
        'actions': ['inferEntryState'],
    },
    {
        'id': 't_entry_done',
        'from': 'inferring_entry',
        'to': 'generating',
        'on_event': 'AUTO',
        'gates': ['hasEntryState'],
        'actions': ['generateBlueprint'],
    },
    {
        'id': 't_generate_done',
        'from': 'generating',
        'to': 'mapping',
        'on_event': 'AUTO',
        'gates': ['hasBlueprint'],
        'actions': ['generateMapping'],
    },
    {
        'id': 't_mapping_done',
        'from': 'mapping',
        'to': 'complete',
        'on_event': 'AUTO',
        'gates': ['hasMapping'],
        'actions': [],
    },
    {
        'id': 't_export_blueprint',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'EXPORT_BLUEPRINT',
        'gates': ['hasBlueprint'],
        'actions': ['exportBlueprint'],
    },
    {
        'id': 't_export_report',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'EXPORT_REPORT',
        'gates': [],
        'actions': ['exportReport'],
    },
    {
        'id': 't_reset',
        'from': 'complete',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clearState'],
    },
    {
        'id': 't_error_reset',
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
    Compiled L++ Operator: Legacy Code State Machine Extractor
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'filePath': None, 'sourceCode': None, 'ast': None, 'analysisMode': None, 'patterns': None, 'extractedStates': None, 'extractedTransitions': None, 'extractedGates': None, 'extractedActions': None, 'extractedEvents': None, 'entryState': None, 'terminalStates': None, 'blueprint': None, 'blueprintJson': None, 'sourceMapping': None, 'uncertainties': None, 'extractionReport': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'filePath': None, 'sourceCode': None, 'ast': None, 'analysisMode': None, 'patterns': None, 'extractedStates': None, 'extractedTransitions': None, 'extractedGates': None, 'extractedActions': None, 'extractedEvents': None, 'entryState': None, 'terminalStates': None, 'blueprint': None, 'blueprintJson': None, 'sourceMapping': None, 'uncertainties': None, 'extractionReport': None, 'error': None}
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
    print('L++ Compiled Operator: Legacy Code State Machine Extractor')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
