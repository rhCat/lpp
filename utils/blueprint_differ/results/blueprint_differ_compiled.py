"""
L++ Compiled Operator: L++ Blueprint Diff & Merge
Version: 1.0.0
Description: Semantic diff and merge tool for L++ blueprints

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

BLUEPRINT_ID = 'lpp_blueprint_differ'
BLUEPRINT_NAME = 'L++ Blueprint Diff & Merge'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprints loaded, waiting for input
    'left_loaded': 'left_loaded',  # Left blueprint loaded, waiting for right
    'ready': 'ready',  # Both blueprints loaded, ready to diff/merge
    'diffing': 'diffing',  # Computing semantic diff
    'diff_complete': 'diff_complete',  # Diff computed, results available
    'merging': 'merging',  # Performing merge operation
    'merge_complete': 'merge_complete',  # Merge complete, result available
    'conflict': 'conflict',  # Merge conflicts detected, awaiting resolution
    'error': 'error',  # Error state
}

GATES = {
    'has_left': 'blueprint_left is not None',
    'has_right': 'blueprint_right is not None',
    'has_both': 'blueprint_left is not None and blueprint_right is not None',
    'has_base': 'blueprint_base is not None',
    'has_diff': 'diff_result is not None',
    'has_conflicts': 'conflicts is not None and len(conflicts) > 0',
    'no_conflicts': 'conflicts is None or len(conflicts) == 0',
    'has_merged': 'merged_blueprint is not None',
    'strategy_is_manual': "merge_strategy == 'manual'",
    'is_three_way': 'blueprint_base is not None',
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprints loaded. Use LOAD_LEFT to start.'},
    {'gate': 'is_left_loaded',
        'template': 'Left: {path_left} | Use LOAD_RIGHT to continue.'},
    {'gate': 'is_ready', 'template': 'Ready: {path_left} vs {path_right}'},
    {'gate': 'is_diff_complete', 'template': 'Diff complete. Use SHOW to view results.'},
    {'gate': 'is_merge_complete', 'template': 'Merge complete. Use EXPORT to save.'},
    {'gate': 'is_conflict', 'template': 'Conflicts detected: {conflicts}'},
    {'template': 'L++ Blueprint Differ'},
]

ACTIONS = {
    'load_left': {
        'type': 'compute',
        'compute_unit': 'diff:load_blueprint',
        'input_map': {'path': 'event.payload.path', 'side': "'left'"},
        'output_map': {'blueprint_left': 'blueprint', 'path_left': 'path', 'error': 'error'},
    },
    'load_right': {
        'type': 'compute',
        'compute_unit': 'diff:load_blueprint',
        'input_map': {'path': 'event.payload.path', 'side': "'right'"},
        'output_map': {'blueprint_right': 'blueprint', 'path_right': 'path', 'error': 'error'},
    },
    'load_base': {
        'type': 'compute',
        'compute_unit': 'diff:load_blueprint',
        'input_map': {'path': 'event.payload.path', 'side': "'base'"},
        'output_map': {'blueprint_base': 'blueprint', 'path_base': 'path', 'error': 'error'},
    },
    'compute_diff': {
        'type': 'compute',
        'compute_unit': 'diff:compute_diff',
        'input_map': {'left': 'blueprint_left', 'right': 'blueprint_right'},
        'output_map': {'diff_result': 'diff'},
    },
    'format_diff_unified': {
        'type': 'compute',
        'compute_unit': 'diff:format_diff',
        'input_map': {'diff': 'diff_result', 'format': "'unified'", 'path_left': 'path_left', 'path_right': 'path_right'},
        'output_map': {'formatted_diff': 'output', 'diff_format': 'format'},
    },
    'format_diff_summary': {
        'type': 'compute',
        'compute_unit': 'diff:format_diff',
        'input_map': {'diff': 'diff_result', 'format': "'summary'", 'path_left': 'path_left', 'path_right': 'path_right'},
        'output_map': {'formatted_diff': 'output', 'diff_format': 'format'},
    },
    'generate_json_patch': {
        'type': 'compute',
        'compute_unit': 'diff:generate_json_patch',
        'input_map': {'diff': 'diff_result'},
        'output_map': {'json_patch': 'patch', 'formatted_diff': 'formatted'},
    },
    'detect_conflicts': {
        'type': 'compute',
        'compute_unit': 'diff:detect_conflicts',
        'input_map': {'left': 'blueprint_left', 'right': 'blueprint_right', 'base': 'blueprint_base', 'diff': 'diff_result'},
        'output_map': {'conflicts': 'conflicts'},
    },
    'merge_take_left': {
        'type': 'compute',
        'compute_unit': 'diff:merge_blueprints',
        'input_map': {'left': 'blueprint_left', 'right': 'blueprint_right', 'base': 'blueprint_base', 'strategy': "'take_left'", 'conflicts': 'conflicts'},
        'output_map': {'merged_blueprint': 'merged', 'merge_strategy': 'strategy'},
    },
    'merge_take_right': {
        'type': 'compute',
        'compute_unit': 'diff:merge_blueprints',
        'input_map': {'left': 'blueprint_left', 'right': 'blueprint_right', 'base': 'blueprint_base', 'strategy': "'take_right'", 'conflicts': 'conflicts'},
        'output_map': {'merged_blueprint': 'merged', 'merge_strategy': 'strategy'},
    },
    'merge_auto': {
        'type': 'compute',
        'compute_unit': 'diff:merge_blueprints',
        'input_map': {'left': 'blueprint_left', 'right': 'blueprint_right', 'base': 'blueprint_base', 'strategy': "'auto'", 'conflicts': 'conflicts'},
        'output_map': {'merged_blueprint': 'merged', 'merge_strategy': 'strategy'},
    },
    'set_strategy_manual': {
        'type': 'set',
        'target': 'merge_strategy',
        'value': 'manual',
    },
    'export_merged': {
        'type': 'compute',
        'compute_unit': 'diff:export_merged',
        'input_map': {'blueprint': 'merged_blueprint', 'path': 'event.payload.path'},
        'output_map': {'export_path': 'path'},
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
    'clear_all': {
        'type': 'compute',
        'compute_unit': 'diff:clear_all',
        'output_map': {'blueprint_left': 'blueprint_left', 'blueprint_right': 'blueprint_right', 'blueprint_base': 'blueprint_base', 'diff_result': 'diff_result', 'conflicts': 'conflicts', 'merged_blueprint': 'merged_blueprint', 'formatted_diff': 'formatted_diff', 'json_patch': 'json_patch'},
    },
    'clear_diff': {
        'type': 'set',
        'target': 'diff_result',
    },
    'clear_merge': {
        'type': 'set',
        'target': 'merged_blueprint',
    },
}

TRANSITIONS = [
    {
        'id': 't_load_left_from_idle',
        'from': 'idle',
        'to': 'left_loaded',
        'on_event': 'LOAD_LEFT',
        'gates': [],
        'actions': ['load_left'],
    },
    {
        'id': 't_load_right_from_left',
        'from': 'left_loaded',
        'to': 'ready',
        'on_event': 'LOAD_RIGHT',
        'gates': [],
        'actions': ['load_right'],
    },
    {
        'id': 't_load_base_from_ready',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD_BASE',
        'gates': [],
        'actions': ['load_base'],
    },
    {
        'id': 't_reload_left',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD_LEFT',
        'gates': [],
        'actions': ['load_left', 'clear_diff', 'clear_merge'],
    },
    {
        'id': 't_reload_right',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD_RIGHT',
        'gates': [],
        'actions': ['load_right', 'clear_diff', 'clear_merge'],
    },
    {
        'id': 't_start_diff',
        'from': 'ready',
        'to': 'diffing',
        'on_event': 'DIFF',
        'gates': ['has_both'],
        'actions': ['compute_diff'],
    },
    {
        'id': 't_diff_to_complete',
        'from': 'diffing',
        'to': 'diff_complete',
        'on_event': 'DIFF_DONE',
        'gates': [],
        'actions': ['format_diff_unified'],
    },
    {
        'id': 't_auto_diff_complete',
        'from': 'ready',
        'to': 'diff_complete',
        'on_event': 'DIFF_ALL',
        'gates': ['has_both'],
        'actions': ['compute_diff', 'format_diff_unified'],
    },
    {
        'id': 't_show_summary',
        'from': 'diff_complete',
        'to': 'diff_complete',
        'on_event': 'SHOW_SUMMARY',
        'gates': ['has_diff'],
        'actions': ['format_diff_summary'],
    },
    {
        'id': 't_show_unified',
        'from': 'diff_complete',
        'to': 'diff_complete',
        'on_event': 'SHOW_UNIFIED',
        'gates': ['has_diff'],
        'actions': ['format_diff_unified'],
    },
    {
        'id': 't_show_patch',
        'from': 'diff_complete',
        'to': 'diff_complete',
        'on_event': 'SHOW_PATCH',
        'gates': ['has_diff'],
        'actions': ['generate_json_patch'],
    },
    {
        'id': 't_start_merge',
        'from': 'diff_complete',
        'to': 'merging',
        'on_event': 'MERGE',
        'gates': ['has_diff'],
        'actions': ['detect_conflicts'],
    },
    {
        'id': 't_merge_no_conflict',
        'from': 'merging',
        'to': 'merge_complete',
        'on_event': 'MERGE_AUTO',
        'gates': ['no_conflicts'],
        'actions': ['merge_auto'],
    },
    {
        'id': 't_merge_conflict_detected',
        'from': 'merging',
        'to': 'conflict',
        'on_event': 'CONFLICT_DETECTED',
        'gates': ['has_conflicts'],
        'actions': ['set_strategy_manual'],
    },
    {
        'id': 't_resolve_take_left',
        'from': 'conflict',
        'to': 'merge_complete',
        'on_event': 'TAKE_LEFT',
        'gates': [],
        'actions': ['merge_take_left'],
    },
    {
        'id': 't_resolve_take_right',
        'from': 'conflict',
        'to': 'merge_complete',
        'on_event': 'TAKE_RIGHT',
        'gates': [],
        'actions': ['merge_take_right'],
    },
    {
        'id': 't_force_merge_left',
        'from': 'diff_complete',
        'to': 'merge_complete',
        'on_event': 'MERGE_LEFT',
        'gates': ['has_diff'],
        'actions': ['detect_conflicts', 'merge_take_left'],
    },
    {
        'id': 't_force_merge_right',
        'from': 'diff_complete',
        'to': 'merge_complete',
        'on_event': 'MERGE_RIGHT',
        'gates': ['has_diff'],
        'actions': ['detect_conflicts', 'merge_take_right'],
    },
    {
        'id': 't_export',
        'from': 'merge_complete',
        'to': 'merge_complete',
        'on_event': 'EXPORT',
        'gates': ['has_merged'],
        'actions': ['export_merged'],
    },
    {
        'id': 't_back_to_diff',
        'from': 'merge_complete',
        'to': 'diff_complete',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_merge'],
    },
    {
        'id': 't_back_from_conflict',
        'from': 'conflict',
        'to': 'diff_complete',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_merge'],
    },
    {
        'id': 't_rediff',
        'from': 'diff_complete',
        'to': 'diff_complete',
        'on_event': 'DIFF_ALL',
        'gates': [],
        'actions': ['compute_diff', 'format_diff_unified'],
    },
    {
        'id': 't_back_to_ready',
        'from': 'diff_complete',
        'to': 'ready',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_diff', 'clear_merge'],
    },
    {
        'id': 't_clear_all',
        'from': 'ready',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_clear_from_diff',
        'from': 'diff_complete',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_clear_from_merge',
        'from': 'merge_complete',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_error_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_error', 'clear_all'],
    },
    {
        'id': 't_load_error',
        'from': '*',
        'to': 'error',
        'on_event': 'LOAD_FAILED',
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
    Compiled L++ Operator: L++ Blueprint Diff & Merge
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint_left': None, 'blueprint_right': None, 'blueprint_base': None, 'path_left': None, 'path_right': None, 'path_base': None, 'diff_result': None,
                        'conflicts': None, 'merged_blueprint': None, 'merge_strategy': None, 'diff_format': None, 'formatted_diff': None, 'json_patch': None, 'export_path': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint_left': None, 'blueprint_right': None, 'blueprint_base': None, 'path_left': None, 'path_right': None, 'path_base': None, 'diff_result': None,
                        'conflicts': None, 'merged_blueprint': None, 'merge_strategy': None, 'diff_format': None, 'formatted_diff': None, 'json_patch': None, 'export_path': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Blueprint Diff & Merge')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
