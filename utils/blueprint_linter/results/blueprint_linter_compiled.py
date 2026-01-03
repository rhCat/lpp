"""
L++ Compiled Operator: L++ Blueprint Linter
Version: 1.0.0
Description: Static analysis tool for L++ blueprints - detects issues and suggests improvements

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

BLUEPRINT_ID = 'lpp_blueprint_linter'
BLUEPRINT_NAME = 'L++ Blueprint Linter'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, ready to lint
    'linting': 'linting',  # Running lint checks
    'complete': 'complete',  # Linting complete, results available
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_findings': 'findings is not None and len(findings) > 0',
    'has_errors': "summary is not None and summary.get('error', 0) > 0",
    'is_clean': "summary is not None and summary.get('error', 0) == 0 and summary.get('warning', 0) == 0",
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprint loaded. Use LOAD command.'},
    {'gate': 'is_complete', 'template': 'Lint complete: {summary.error} errors, {summary.warning} warnings'},
    {'gate': 'is_linting', 'template': 'Linting in progress...'},
    {'gate': 'is_loaded', 'template': 'Loaded: {blueprint_path}'},
    {'template': 'L++ Blueprint Linter'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'lint:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'path', 'error': 'error'},
    },
    'init_lint': {
        'type': 'compute',
        'compute_unit': 'lint:init_lint',
        'input_map': {'config': 'lint_config'},
        'output_map': {'findings': 'findings', 'summary': 'summary', 'metrics': 'metrics'},
    },
    'check_unreachable_states': {
        'type': 'compute',
        'compute_unit': 'lint:check_unreachable_states',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_dead_end_states': {
        'type': 'compute',
        'compute_unit': 'lint:check_dead_end_states',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_unused_gates': {
        'type': 'compute',
        'compute_unit': 'lint:check_unused_gates',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_unused_actions': {
        'type': 'compute',
        'compute_unit': 'lint:check_unused_actions',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_unused_context': {
        'type': 'compute',
        'compute_unit': 'lint:check_unused_context',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_orphaned_transitions': {
        'type': 'compute',
        'compute_unit': 'lint:check_orphaned_transitions',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_missing_gate_refs': {
        'type': 'compute',
        'compute_unit': 'lint:check_missing_gate_refs',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_missing_action_refs': {
        'type': 'compute',
        'compute_unit': 'lint:check_missing_action_refs',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_duplicate_ids': {
        'type': 'compute',
        'compute_unit': 'lint:check_duplicate_ids',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'check_naming_conventions': {
        'type': 'compute',
        'compute_unit': 'lint:check_naming_conventions',
        'input_map': {'blueprint': 'blueprint', 'findings': 'findings'},
        'output_map': {'findings': 'findings'},
    },
    'compute_metrics': {
        'type': 'compute',
        'compute_unit': 'lint:compute_metrics',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'metrics': 'metrics'},
    },
    'compute_summary': {
        'type': 'compute',
        'compute_unit': 'lint:compute_summary',
        'input_map': {'findings': 'findings'},
        'output_map': {'summary': 'summary'},
    },
    'generate_report': {
        'type': 'compute',
        'compute_unit': 'lint:generate_report',
        'input_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'findings': 'findings', 'summary': 'summary', 'metrics': 'metrics'},
        'output_map': {'report': 'report'},
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
    'clear_findings': {
        'type': 'set',
        'target': 'findings',
    },
    'unload_blueprint': {
        'type': 'set',
        'target': 'blueprint',
    },
    'set_config': {
        'type': 'set',
        'target': 'lint_config',
        'value_from': 'event.payload.config',
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
        'actions': ['load_blueprint', 'clear_findings'],
    },
    {
        'id': 't_reload_from_complete',
        'from': 'complete',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'clear_findings'],
    },
    {
        'id': 't_start_lint',
        'from': 'loaded',
        'to': 'linting',
        'on_event': 'LINT',
        'gates': ['has_blueprint'],
        'actions': ['init_lint'],
    },
    {
        'id': 't_check_unreachable',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_UNREACHABLE',
        'gates': [],
        'actions': ['check_unreachable_states'],
    },
    {
        'id': 't_check_dead_end',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_DEAD_END',
        'gates': [],
        'actions': ['check_dead_end_states'],
    },
    {
        'id': 't_check_unused_gates',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_UNUSED_GATES',
        'gates': [],
        'actions': ['check_unused_gates'],
    },
    {
        'id': 't_check_unused_actions',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_UNUSED_ACTIONS',
        'gates': [],
        'actions': ['check_unused_actions'],
    },
    {
        'id': 't_check_unused_context',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_UNUSED_CONTEXT',
        'gates': [],
        'actions': ['check_unused_context'],
    },
    {
        'id': 't_check_orphaned',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_ORPHANED',
        'gates': [],
        'actions': ['check_orphaned_transitions'],
    },
    {
        'id': 't_check_gate_refs',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_GATE_REFS',
        'gates': [],
        'actions': ['check_missing_gate_refs'],
    },
    {
        'id': 't_check_action_refs',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_ACTION_REFS',
        'gates': [],
        'actions': ['check_missing_action_refs'],
    },
    {
        'id': 't_check_duplicates',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_DUPLICATES',
        'gates': [],
        'actions': ['check_duplicate_ids'],
    },
    {
        'id': 't_check_naming',
        'from': 'linting',
        'to': 'linting',
        'on_event': 'CHECK_NAMING',
        'gates': [],
        'actions': ['check_naming_conventions'],
    },
    {
        'id': 't_finalize',
        'from': 'linting',
        'to': 'complete',
        'on_event': 'FINALIZE',
        'gates': [],
        'actions': ['compute_metrics', 'compute_summary', 'generate_report'],
    },
    {
        'id': 't_run_all',
        'from': 'loaded',
        'to': 'complete',
        'on_event': 'LINT_ALL',
        'gates': ['has_blueprint'],
        'actions': ['init_lint', 'check_unreachable_states', 'check_dead_end_states', 'check_unused_gates', 'check_unused_actions', 'check_unused_context', 'check_orphaned_transitions', 'check_missing_gate_refs', 'check_missing_action_refs', 'check_duplicate_ids', 'check_naming_conventions', 'compute_metrics', 'compute_summary', 'generate_report'],
    },
    {
        'id': 't_relint',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'LINT_ALL',
        'gates': ['has_blueprint'],
        'actions': ['init_lint', 'check_unreachable_states', 'check_dead_end_states', 'check_unused_gates', 'check_unused_actions', 'check_unused_context', 'check_orphaned_transitions', 'check_missing_gate_refs', 'check_missing_action_refs', 'check_duplicate_ids', 'check_naming_conventions', 'compute_metrics', 'compute_summary', 'generate_report'],
    },
    {
        'id': 't_back_to_loaded',
        'from': 'complete',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_findings'],
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
        'id': 't_unload_from_complete',
        'from': 'complete',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint', 'clear_findings'],
    },
    {
        'id': 't_configure',
        'from': 'idle',
        'to': 'idle',
        'on_event': 'CONFIGURE',
        'gates': [],
        'actions': ['set_config'],
    },
    {
        'id': 't_configure_loaded',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'CONFIGURE',
        'gates': [],
        'actions': ['set_config'],
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
    Compiled L++ Operator: L++ Blueprint Linter
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'findings': None, 'summary': None, 'metrics': None, 'report': None, 'error': None, 'lint_config': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'findings': None, 'summary': None, 'metrics': None, 'report': None, 'error': None, 'lint_config': None}
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
    print('L++ Compiled Operator: L++ Blueprint Linter')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
