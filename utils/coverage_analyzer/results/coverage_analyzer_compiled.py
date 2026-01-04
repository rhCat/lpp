"""
L++ Compiled Operator: L++ Coverage Analyzer
Version: 1.0.0
Description: Tracks runtime coverage of blueprints during execution

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

BLUEPRINT_ID = 'coverage_analyzer'
BLUEPRINT_NAME = 'L++ Coverage Analyzer'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, coverage tracking initialized
    'tracking': 'tracking',  # Actively tracking coverage data
    'analyzing': 'analyzing',  # Computing coverage metrics
    'reporting': 'reporting',  # Generating reports
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_coverage': 'coverage_data is not None',
    'has_metrics': 'metrics is not None',
    'has_summary': 'summary_report is not None',
    'has_detailed': 'detailed_report is not None',
    'has_gap': 'gap_report is not None',
    'has_html': 'html_report is not None',
    'has_json': 'json_report is not None',
    'has_trace': 'trace_data is not None and len(trace_data) > 0',
    'is_tracking': "_state == 'tracking'",
    'is_loaded': "_state == 'loaded'",
}

DISPLAY_RULES = [
    {'gate': 'has_metrics', 'template': 'Coverage: {metrics.overall_percentage}% - States: {metrics.state_percentage}% | Trans: {metrics.transition_percentage}%'},
    {'gate': 'has_blueprint',
        'template': 'Loaded: {blueprint.name} (tracking)'},
    {'template': 'L++ Coverage Analyzer'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'cov:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'path', 'error': 'error'},
    },
    'init_coverage': {
        'type': 'compute',
        'compute_unit': 'cov:init_coverage',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'coverage_data': 'coverage_data', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits'},
    },
    'record_state': {
        'type': 'compute',
        'compute_unit': 'cov:record_state',
        'input_map': {'state_hits': 'state_hits', 'state_id': 'event.payload.state_id'},
        'output_map': {'state_hits': 'state_hits'},
    },
    'record_transition': {
        'type': 'compute',
        'compute_unit': 'cov:record_transition',
        'input_map': {'transition_hits': 'transition_hits', 'transition_id': 'event.payload.transition_id'},
        'output_map': {'transition_hits': 'transition_hits'},
    },
    'record_gate': {
        'type': 'compute',
        'compute_unit': 'cov:record_gate',
        'input_map': {'gate_hits': 'gate_hits', 'gate_id': 'event.payload.gate_id', 'result': 'event.payload.result'},
        'output_map': {'gate_hits': 'gate_hits'},
    },
    'record_action': {
        'type': 'compute',
        'compute_unit': 'cov:record_action',
        'input_map': {'action_hits': 'action_hits', 'action_id': 'event.payload.action_id'},
        'output_map': {'action_hits': 'action_hits'},
    },
    'record_event': {
        'type': 'compute',
        'compute_unit': 'cov:record_event',
        'input_map': {'event_hits': 'event_hits', 'event_name': 'event.payload.event_name'},
        'output_map': {'event_hits': 'event_hits'},
    },
    'import_trace': {
        'type': 'compute',
        'compute_unit': 'cov:import_trace',
        'input_map': {'path': 'event.payload.path', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits'},
        'output_map': {'trace_data': 'trace_data', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits', 'error': 'error'},
    },
    'compute_metrics': {
        'type': 'compute',
        'compute_unit': 'cov:compute_metrics',
        'input_map': {'blueprint': 'blueprint', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits'},
        'output_map': {'metrics': 'metrics'},
    },
    'generate_summary': {
        'type': 'compute',
        'compute_unit': 'cov:generate_summary',
        'input_map': {'blueprint': 'blueprint', 'metrics': 'metrics'},
        'output_map': {'summary_report': 'report'},
    },
    'generate_detailed': {
        'type': 'compute',
        'compute_unit': 'cov:generate_detailed',
        'input_map': {'blueprint': 'blueprint', 'metrics': 'metrics', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits'},
        'output_map': {'detailed_report': 'report'},
    },
    'generate_gap_report': {
        'type': 'compute',
        'compute_unit': 'cov:generate_gap_report',
        'input_map': {'blueprint': 'blueprint', 'metrics': 'metrics', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits'},
        'output_map': {'gap_report': 'report'},
    },
    'export_html': {
        'type': 'compute',
        'compute_unit': 'cov:export_html',
        'input_map': {'blueprint': 'blueprint', 'metrics': 'metrics', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'path': 'event.payload.path'},
        'output_map': {'html_report': 'html', 'export_path': 'path'},
    },
    'export_json': {
        'type': 'compute',
        'compute_unit': 'cov:export_json',
        'input_map': {'blueprint': 'blueprint', 'metrics': 'metrics', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits', 'path': 'event.payload.path'},
        'output_map': {'json_report': 'json', 'export_path': 'path'},
    },
    'reset_coverage': {
        'type': 'compute',
        'compute_unit': 'cov:reset_coverage',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'coverage_data': 'coverage_data', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits', 'metrics': 'metrics', 'summary_report': 'summary_report', 'detailed_report': 'detailed_report', 'gap_report': 'gap_report', 'html_report': 'html_report', 'json_report': 'json_report'},
    },
    'clear_all': {
        'type': 'compute',
        'compute_unit': 'cov:clear_all',
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'coverage_data': 'coverage_data', 'state_hits': 'state_hits', 'transition_hits': 'transition_hits', 'gate_hits': 'gate_hits', 'action_hits': 'action_hits', 'event_hits': 'event_hits', 'metrics': 'metrics', 'summary_report': 'summary_report', 'detailed_report': 'detailed_report', 'gap_report': 'gap_report', 'html_report': 'html_report', 'json_report': 'json_report', 'trace_data': 'trace_data', 'error': 'error'},
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
        'actions': ['load_blueprint', 'init_coverage'],
    },
    {
        'id': 't_reload',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['clear_all', 'load_blueprint', 'init_coverage'],
    },
    {
        'id': 't_reload_from_tracking',
        'from': 'tracking',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['clear_all', 'load_blueprint', 'init_coverage'],
    },
    {
        'id': 't_reload_from_analyzing',
        'from': 'analyzing',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['clear_all', 'load_blueprint', 'init_coverage'],
    },
    {
        'id': 't_reload_from_reporting',
        'from': 'reporting',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['clear_all', 'load_blueprint', 'init_coverage'],
    },
    {
        'id': 't_start_tracking',
        'from': 'loaded',
        'to': 'tracking',
        'on_event': 'START',
        'gates': ['has_blueprint'],
        'actions': [],
    },
    {
        'id': 't_record_state',
        'from': 'tracking',
        'to': 'tracking',
        'on_event': 'STATE',
        'gates': [],
        'actions': ['record_state'],
    },
    {
        'id': 't_record_transition',
        'from': 'tracking',
        'to': 'tracking',
        'on_event': 'TRANSITION',
        'gates': [],
        'actions': ['record_transition'],
    },
    {
        'id': 't_record_gate',
        'from': 'tracking',
        'to': 'tracking',
        'on_event': 'GATE',
        'gates': [],
        'actions': ['record_gate'],
    },
    {
        'id': 't_record_action',
        'from': 'tracking',
        'to': 'tracking',
        'on_event': 'ACTION',
        'gates': [],
        'actions': ['record_action'],
    },
    {
        'id': 't_record_event',
        'from': 'tracking',
        'to': 'tracking',
        'on_event': 'EVENT',
        'gates': [],
        'actions': ['record_event'],
    },
    {
        'id': 't_import_trace_loaded',
        'from': 'loaded',
        'to': 'tracking',
        'on_event': 'IMPORT',
        'gates': ['has_blueprint'],
        'actions': ['import_trace'],
    },
    {
        'id': 't_import_trace_tracking',
        'from': 'tracking',
        'to': 'tracking',
        'on_event': 'IMPORT',
        'gates': [],
        'actions': ['import_trace'],
    },
    {
        'id': 't_analyze',
        'from': 'tracking',
        'to': 'analyzing',
        'on_event': 'ANALYZE',
        'gates': ['has_coverage'],
        'actions': ['compute_metrics'],
    },
    {
        'id': 't_analyze_from_loaded',
        'from': 'loaded',
        'to': 'analyzing',
        'on_event': 'ANALYZE',
        'gates': ['has_blueprint'],
        'actions': ['compute_metrics'],
    },
    {
        'id': 't_summary',
        'from': 'analyzing',
        'to': 'reporting',
        'on_event': 'SUMMARY',
        'gates': ['has_metrics'],
        'actions': ['generate_summary'],
    },
    {
        'id': 't_detailed',
        'from': 'analyzing',
        'to': 'reporting',
        'on_event': 'DETAILED',
        'gates': ['has_metrics'],
        'actions': ['generate_detailed'],
    },
    {
        'id': 't_gap',
        'from': 'analyzing',
        'to': 'reporting',
        'on_event': 'GAP',
        'gates': ['has_metrics'],
        'actions': ['generate_gap_report'],
    },
    {
        'id': 't_all_reports',
        'from': 'analyzing',
        'to': 'reporting',
        'on_event': 'ALL_REPORTS',
        'gates': ['has_metrics'],
        'actions': ['generate_summary', 'generate_detailed', 'generate_gap_report'],
    },
    {
        'id': 't_export_html',
        'from': 'reporting',
        'to': 'reporting',
        'on_event': 'EXPORT_HTML',
        'gates': ['has_metrics'],
        'actions': ['export_html'],
    },
    {
        'id': 't_export_html_from_analyzing',
        'from': 'analyzing',
        'to': 'reporting',
        'on_event': 'EXPORT_HTML',
        'gates': ['has_metrics'],
        'actions': ['export_html'],
    },
    {
        'id': 't_export_json',
        'from': 'reporting',
        'to': 'reporting',
        'on_event': 'EXPORT_JSON',
        'gates': ['has_metrics'],
        'actions': ['export_json'],
    },
    {
        'id': 't_export_json_from_analyzing',
        'from': 'analyzing',
        'to': 'reporting',
        'on_event': 'EXPORT_JSON',
        'gates': ['has_metrics'],
        'actions': ['export_json'],
    },
    {
        'id': 't_more_summary',
        'from': 'reporting',
        'to': 'reporting',
        'on_event': 'SUMMARY',
        'gates': ['has_metrics'],
        'actions': ['generate_summary'],
    },
    {
        'id': 't_more_detailed',
        'from': 'reporting',
        'to': 'reporting',
        'on_event': 'DETAILED',
        'gates': ['has_metrics'],
        'actions': ['generate_detailed'],
    },
    {
        'id': 't_more_gap',
        'from': 'reporting',
        'to': 'reporting',
        'on_event': 'GAP',
        'gates': ['has_metrics'],
        'actions': ['generate_gap_report'],
    },
    {
        'id': 't_reset',
        'from': 'tracking',
        'to': 'loaded',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['reset_coverage'],
    },
    {
        'id': 't_reset_from_analyzing',
        'from': 'analyzing',
        'to': 'loaded',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['reset_coverage'],
    },
    {
        'id': 't_reset_from_reporting',
        'from': 'reporting',
        'to': 'loaded',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['reset_coverage'],
    },
    {
        'id': 't_back_to_tracking',
        'from': 'analyzing',
        'to': 'tracking',
        'on_event': 'BACK',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_back_to_analyzing',
        'from': 'reporting',
        'to': 'analyzing',
        'on_event': 'BACK',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_unload',
        'from': 'loaded',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_unload_from_tracking',
        'from': 'tracking',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_unload_from_analyzing',
        'from': 'analyzing',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_unload_from_reporting',
        'from': 'reporting',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_error',
        'from': '*',
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
        'actions': ['clear_error', 'clear_all'],
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
    Compiled L++ Operator: L++ Coverage Analyzer
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'coverage_data': None, 'state_hits': None, 'transition_hits': None, 'gate_hits': None, 'action_hits': None,
                        'event_hits': None, 'metrics': None, 'summary_report': None, 'detailed_report': None, 'gap_report': None, 'html_report': None, 'json_report': None, 'export_path': None, 'trace_data': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'coverage_data': None, 'state_hits': None, 'transition_hits': None, 'gate_hits': None, 'action_hits': None,
                        'event_hits': None, 'metrics': None, 'summary_report': None, 'detailed_report': None, 'gap_report': None, 'html_report': None, 'json_report': None, 'export_path': None, 'trace_data': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Coverage Analyzer')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
