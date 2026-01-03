"""
L++ Compiled Operator: L++ Compliance Checker
Version: 1.0.0
Description: Verifies L++ blueprints against compliance policies

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

BLUEPRINT_ID = 'compliance_checker'
BLUEPRINT_NAME = 'L++ Compliance Checker'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'blueprint_loaded': 'blueprint_loaded',  # Blueprint loaded, ready to load policies
    'ready': 'ready',  # Blueprint and policies loaded, ready to check
    'checking': 'checking',  # Running compliance checks
    'report_ready': 'report_ready',  # Compliance report generated
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_policies': 'policies is not None and len(policies) > 0',
    'no_policies': 'policies is None or len(policies) == 0',
    'has_findings': 'findings is not None and len(findings) > 0',
    'has_report': 'report is not None',
    'is_idle': "_state == 'idle'",
    'is_ready': "_state == 'ready'",
    'is_checking': "_state == 'checking'",
    'is_report_ready': "_state == 'report_ready'",
    'is_error': "_state == 'error'",
    'score_passing': 'score is not None and score >= 80',
    'score_warning': 'score is not None and score >= 50 and score < 80',
    'score_failing': 'score is not None and score < 50',
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprint loaded. Use LOAD command.'},
    {'gate': 'is_report_ready', 'template': 'Report Ready | Score: {score}% | {blueprint_name}'},
    {'gate': 'is_ready', 'template': 'Ready | {blueprint_name} | Policies: {policies}'},
    {'gate': 'has_blueprint', 'template': 'Loaded: {blueprint_name}'},
    {'template': 'L++ Compliance Checker'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'compliance:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'blueprint_name': 'blueprint_name', 'error': 'error'},
    },
    'load_policy': {
        'type': 'compute',
        'compute_unit': 'compliance:load_policy',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'policies': 'policies', 'error': 'error'},
    },
    'load_policies': {
        'type': 'compute',
        'compute_unit': 'compliance:load_policies',
        'input_map': {'dir_path': 'event.payload.dir_path'},
        'output_map': {'policies': 'policies', 'policies_dir': 'policies_dir', 'error': 'error'},
    },
    'check_policy': {
        'type': 'compute',
        'compute_unit': 'compliance:check_policy',
        'input_map': {'blueprint': 'blueprint', 'policy': 'event.payload.policy'},
        'output_map': {'findings': 'findings', 'error': 'error'},
    },
    'check_all_policies': {
        'type': 'compute',
        'compute_unit': 'compliance:check_all_policies',
        'input_map': {'blueprint': 'blueprint', 'policies': 'policies'},
        'output_map': {'findings': 'findings', 'summary': 'summary', 'error': 'error'},
    },
    'generate_report': {
        'type': 'compute',
        'compute_unit': 'compliance:generate_report',
        'input_map': {'blueprint': 'blueprint', 'blueprint_name': 'blueprint_name', 'policies': 'policies', 'findings': 'findings', 'summary': 'summary'},
        'output_map': {'report': 'report', 'score': 'score'},
    },
    'calculate_score': {
        'type': 'compute',
        'compute_unit': 'compliance:calculate_score',
        'input_map': {'findings': 'findings', 'policies': 'policies'},
        'output_map': {'score': 'score'},
    },
    'export_report': {
        'type': 'compute',
        'compute_unit': 'compliance:export_report',
        'input_map': {'report': 'report', 'output_path': 'event.payload.path', 'format': 'event.payload.format'},
        'output_map': {'export_path': 'export_path', 'error': 'error'},
    },
    'select_policy': {
        'type': 'set',
        'target': 'current_policy',
        'value_from': 'event.payload.policy',
    },
    'clear_policy': {
        'type': 'set',
        'target': 'current_policy',
    },
    'clear_findings': {
        'type': 'set',
        'target': 'findings',
    },
    'clear_report': {
        'type': 'set',
        'target': 'report',
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
    'unload_blueprint': {
        'type': 'set',
        'target': 'blueprint',
    },
    'unload_policies': {
        'type': 'set',
        'target': 'policies',
    },
}

TRANSITIONS = [
    {
        'id': 't_load_blueprint',
        'from': 'idle',
        'to': 'blueprint_loaded',
        'on_event': 'LOAD_BLUEPRINT',
        'gates': ['no_blueprint'],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_load_blueprint_error',
        'from': 'idle',
        'to': 'error',
        'on_event': 'LOAD_FAILED',
        'gates': [],
        'actions': ['set_error'],
    },
    {
        'id': 't_reload_blueprint',
        'from': 'blueprint_loaded',
        'to': 'blueprint_loaded',
        'on_event': 'LOAD_BLUEPRINT',
        'gates': [],
        'actions': ['load_blueprint', 'clear_findings', 'clear_report'],
    },
    {
        'id': 't_reload_blueprint_ready',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD_BLUEPRINT',
        'gates': [],
        'actions': ['load_blueprint', 'clear_findings', 'clear_report'],
    },
    {
        'id': 't_reload_blueprint_report',
        'from': 'report_ready',
        'to': 'ready',
        'on_event': 'LOAD_BLUEPRINT',
        'gates': [],
        'actions': ['load_blueprint', 'clear_findings', 'clear_report'],
    },
    {
        'id': 't_load_policies',
        'from': 'blueprint_loaded',
        'to': 'ready',
        'on_event': 'LOAD_POLICIES',
        'gates': ['has_blueprint'],
        'actions': ['load_policies'],
    },
    {
        'id': 't_load_single_policy',
        'from': 'blueprint_loaded',
        'to': 'ready',
        'on_event': 'LOAD_POLICY',
        'gates': ['has_blueprint'],
        'actions': ['load_policy'],
    },
    {
        'id': 't_reload_policies',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD_POLICIES',
        'gates': [],
        'actions': ['load_policies', 'clear_findings', 'clear_report'],
    },
    {
        'id': 't_reload_policies_report',
        'from': 'report_ready',
        'to': 'ready',
        'on_event': 'LOAD_POLICIES',
        'gates': [],
        'actions': ['load_policies', 'clear_findings', 'clear_report'],
    },
    {
        'id': 't_add_policy',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD_POLICY',
        'gates': [],
        'actions': ['load_policy'],
    },
    {
        'id': 't_check_all',
        'from': 'ready',
        'to': 'checking',
        'on_event': 'CHECK',
        'gates': ['has_blueprint', 'has_policies'],
        'actions': ['check_all_policies'],
    },
    {
        'id': 't_check_single',
        'from': 'ready',
        'to': 'checking',
        'on_event': 'CHECK_POLICY',
        'gates': ['has_blueprint'],
        'actions': ['check_policy'],
    },
    {
        'id': 't_generate_report',
        'from': 'checking',
        'to': 'report_ready',
        'on_event': 'GENERATE_REPORT',
        'gates': ['has_findings'],
        'actions': ['generate_report'],
    },
    {
        'id': 't_auto_report',
        'from': 'checking',
        'to': 'report_ready',
        'on_event': 'AUTO',
        'gates': [],
        'actions': ['generate_report'],
    },
    {
        'id': 't_export_report',
        'from': 'report_ready',
        'to': 'report_ready',
        'on_event': 'EXPORT',
        'gates': ['has_report'],
        'actions': ['export_report'],
    },
    {
        'id': 't_recheck',
        'from': 'report_ready',
        'to': 'checking',
        'on_event': 'CHECK',
        'gates': ['has_blueprint', 'has_policies'],
        'actions': ['clear_report', 'check_all_policies'],
    },
    {
        'id': 't_back_to_ready',
        'from': 'report_ready',
        'to': 'ready',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_report'],
    },
    {
        'id': 't_back_to_loaded',
        'from': 'ready',
        'to': 'blueprint_loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['unload_policies', 'clear_findings'],
    },
    {
        'id': 't_unload',
        'from': 'blueprint_loaded',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint'],
    },
    {
        'id': 't_unload_ready',
        'from': 'ready',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint', 'unload_policies', 'clear_findings'],
    },
    {
        'id': 't_unload_report',
        'from': 'report_ready',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint', 'unload_policies', 'clear_findings', 'clear_report'],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_error'],
    },
    {
        'id': 't_global_error',
        'from': '*',
        'to': 'error',
        'on_event': 'ERROR',
        'gates': [],
        'actions': ['set_error'],
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
    Compiled L++ Operator: L++ Compliance Checker
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'policies': None, 'policies_dir': None, 'current_policy': None, 'findings': None, 'report': None, 'score': None, 'summary': None, 'export_path': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'policies': None, 'policies_dir': None, 'current_policy': None, 'findings': None, 'report': None, 'score': None, 'summary': None, 'export_path': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Compliance Checker')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
