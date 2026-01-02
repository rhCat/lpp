"""
L++ Compiled Operator: Skill Registry
Version: 1.0.0
Description: Scan and document L++ skills for agent blueprint generation

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

BLUEPRINT_ID = 'skill_registry'
BLUEPRINT_NAME = 'Skill Registry'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # Ready to scan
    'scanned': 'scanned',  # Skills discovered
    'viewing': 'viewing',  # Viewing skill detail
    'error': 'error',  # Error occurred
}

GATES = {
    'hasPath': 'basePath is not None',
    'hasSkills': 'skills is not None',
    'hasSelection': 'selectedSkill is not None',
    'hasRegistry': 'registry is not None',
    'hasError': 'error is not None',
    'noError': 'error is None',
}

DISPLAY_RULES = [
    {'gate': 'hasError', 'template': 'Error: {error}'},
    {'gate': 'hasSelection', 'template': 'Viewing: {selectedSkill.name}'},
    {'gate': 'hasSkills', 'template': 'Found {skills.length} skills in {basePath}'},
    {'template': 'Ready to scan'},
]

ACTIONS = {
    'setBasePath': {
        'type': 'set',
        'target': 'basePath',
        'value_from': 'event.payload.path',
    },
    'scanSkills': {
        'type': 'compute',
        'compute_unit': 'registry:scan',
        'input_map': {'basePath': 'basePath'},
        'output_map': {'skills': 'skills', 'error': 'error'},
    },
    'setSelectedId': {
        'type': 'set',
        'target': 'selectedId',
        'value_from': 'event.payload.skillId',
    },
    'loadSkillDetail': {
        'type': 'compute',
        'compute_unit': 'registry:loadDetail',
        'input_map': {'skillId': 'event.payload.skillId', 'basePath': 'basePath'},
        'output_map': {'selectedSkill': 'selectedSkill', 'error': 'error'},
    },
    'exportRegistry': {
        'type': 'compute',
        'compute_unit': 'registry:export',
        'input_map': {'skills': 'skills', 'basePath': 'basePath'},
        'output_map': {'registry': 'registry', 'error': 'error'},
    },
    'clearSelection': {
        'type': 'set',
        'target': 'selectedSkill',
    },
    'clearError': {
        'type': 'set',
        'target': 'error',
    },
}

TRANSITIONS = [
    {
        'id': 't_scan',
        'from': 'idle',
        'to': 'scanned',
        'on_event': 'SCAN',
        'gates': [],
        'actions': ['setBasePath', 'scanSkills'],
    },
    {
        'id': 't_rescan',
        'from': 'scanned',
        'to': 'scanned',
        'on_event': 'SCAN',
        'gates': [],
        'actions': ['clearSelection', 'setBasePath', 'scanSkills'],
    },
    {
        'id': 't_select',
        'from': 'scanned',
        'to': 'viewing',
        'on_event': 'SELECT',
        'gates': [],
        'actions': ['loadSkillDetail'],
    },
    {
        'id': 't_back',
        'from': 'viewing',
        'to': 'scanned',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clearSelection'],
    },
    {
        'id': 't_select_another',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'SELECT',
        'gates': [],
        'actions': ['loadSkillDetail'],
    },
    {
        'id': 't_export',
        'from': 'scanned',
        'to': 'scanned',
        'on_event': 'EXPORT',
        'gates': [],
        'actions': ['exportRegistry'],
    },
    {
        'id': 't_export_viewing',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'EXPORT',
        'gates': [],
        'actions': ['exportRegistry'],
    },
    {
        'id': 't_reset',
        'from': 'scanned',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clearSelection'],
    },
    {
        'id': 't_retry',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RETRY',
        'gates': [],
        'actions': ['clearError'],
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
    Compiled L++ Operator: Skill Registry
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'basePath': None, 'skills': None,
                        'selectedSkill': None, 'registry': None, 'error': None}
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
                    # Sync scope for chained actions
                    scope.update(self.context)

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
        self.context = {'_state': ENTRY_STATE, 'basePath': None, 'skills': None,
                        'selectedSkill': None, 'registry': None, 'error': None}
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
    print('L++ Compiled Operator: Skill Registry')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
