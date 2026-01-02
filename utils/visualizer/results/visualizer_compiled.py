"""
L++ Compiled Operator: L++ Blueprint Visualizer
Version: 1.1.0
Description: L++ visualizing itself - a meta-example demonstrating self-reference

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

BLUEPRINT_ID = 'lpp_visualizer'
BLUEPRINT_NAME = 'L++ Blueprint Visualizer'
BLUEPRINT_VERSION = '1.1.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, ready to visualize
    'viewing': 'viewing',  # Actively viewing/exploring the blueprint
    'exporting': 'exporting',  # Generating export output
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'is_idle': "_state == 'idle'",
    'is_loaded': "_state == 'loaded'",
    'is_viewing': "_state == 'viewing'",
    'is_error': "_state == 'error'",
    'view_is_graph': "view_mode == 'graph'",
    'view_is_table': "view_mode == 'table'",
    'view_is_mermaid': "view_mode == 'mermaid'",
    'has_selection': 'selected_node is not None',
    'can_zoom_in': 'zoom_level < 2.0',
    'can_zoom_out': 'zoom_level > 0.5',
    'has_states': 'blueprint is not None and len(blueprint.states) > 0',
    'has_transitions': 'blueprint is not None and len(blueprint.transitions) > 0',
    'has_tree': 'tree is not None',
    'no_tree': 'tree is None',
    'view_is_tree': "view_mode == 'tree'",
    'view_is_tree_mermaid': "view_mode == 'tree_mermaid'",
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': '❌ ERROR: {error}'},
    {'gate': 'is_idle', 'template': '📂 No blueprint loaded. Use LOAD command.'},
    {'gate': 'is_viewing', 'template': '[{view_mode}] Viewing: {blueprint_name} | Zoom: {zoom_level}x'},
    {'gate': 'has_tree', 'template': '[tree] {tree_name}'},
    {'gate': 'is_loaded', 'template': '✅ Loaded: {blueprint_name} ({blueprint_id})'},
    {'gate': 'is_exporting', 'template': '📤 Exporting...'},
    {'template': 'L++ Visualizer'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'viz:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_name': 'blueprint_name', 'blueprint_id': 'blueprint_id', 'error': 'error'},
    },
    'set_view_graph': {
        'type': 'set',
        'target': 'view_mode',
        'value': 'graph',
    },
    'set_view_table': {
        'type': 'set',
        'target': 'view_mode',
        'value': 'table',
    },
    'set_view_mermaid': {
        'type': 'set',
        'target': 'view_mode',
        'value': 'mermaid',
    },
    'select_node': {
        'type': 'set',
        'target': 'selected_node',
        'value_from': 'event.payload.node_id',
    },
    'clear_selection': {
        'type': 'set',
        'target': 'selected_node',
    },
    'zoom_in': {
        'type': 'compute',
        'compute_unit': 'viz:zoom',
        'input_map': {'current': 'zoom_level', 'direction': 1},
        'output_map': {'zoom_level': 'new_level'},
    },
    'zoom_out': {
        'type': 'compute',
        'compute_unit': 'viz:zoom',
        'input_map': {'current': 'zoom_level', 'direction': -1},
        'output_map': {'zoom_level': 'new_level'},
    },
    'toggle_gates': {
        'type': 'compute',
        'compute_unit': 'viz:toggle',
        'input_map': {'current': 'show_gates'},
        'output_map': {'show_gates': 'result'},
    },
    'toggle_actions': {
        'type': 'compute',
        'compute_unit': 'viz:toggle',
        'input_map': {'current': 'show_actions'},
        'output_map': {'show_actions': 'result'},
    },
    'render_graph': {
        'type': 'compute',
        'compute_unit': 'viz:render_graph',
        'input_map': {'blueprint': 'blueprint', 'selected': 'selected_node', 'show_gates': 'show_gates', 'show_actions': 'show_actions'},
        'output_map': {'output': 'rendered'},
    },
    'render_table': {
        'type': 'compute',
        'compute_unit': 'viz:render_table',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'output': 'rendered'},
    },
    'render_mermaid': {
        'type': 'compute',
        'compute_unit': 'viz:render_mermaid',
        'input_map': {'blueprint': 'blueprint', 'show_gates': 'show_gates'},
        'output_map': {'output': 'rendered'},
    },
    'load_tree': {
        'type': 'compute',
        'compute_unit': 'viz:load_tree',
        'input_map': {'path': 'event.payload.path', 'tree_key': 'event.payload.tree_key'},
        'output_map': {'tree': 'tree', 'tree_name': 'tree_name', 'error': 'error'},
    },
    'set_tree': {
        'type': 'set',
        'target': 'tree',
        'value_from': 'event.payload.tree',
    },
    'render_tree': {
        'type': 'compute',
        'compute_unit': 'viz:render_tree',
        'input_map': {'tree': 'tree', 'show_status': 'show_gates', 'show_desc': 'show_actions'},
        'output_map': {'tree_output': 'rendered'},
    },
    'render_tree_mermaid': {
        'type': 'compute',
        'compute_unit': 'viz:render_tree_mermaid',
        'input_map': {'tree': 'tree', 'title': 'tree_name'},
        'output_map': {'tree_output': 'rendered'},
    },
    'set_view_tree': {
        'type': 'set',
        'target': 'view_mode',
        'value': 'tree',
    },
    'set_view_tree_mermaid': {
        'type': 'set',
        'target': 'view_mode',
        'value': 'tree_mermaid',
    },
    'unload_tree': {
        'type': 'set',
        'target': 'tree',
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
    'init_defaults': {
        'type': 'compute',
        'compute_unit': 'viz:init_defaults',
        'output_map': {'view_mode': 'view_mode', 'zoom_level': 'zoom_level', 'show_gates': 'show_gates', 'show_actions': 'show_actions'},
    },
    'unload_blueprint': {
        'type': 'set',
        'target': 'blueprint',
    },
    'generate_readme': {
        'type': 'compute',
        'compute_unit': 'viz:generate_readme',
        'input_map': {'blueprint': 'blueprint', 'include_mermaid': 'show_gates', 'include_tables': 'show_actions'},
        'output_map': {'readme_content': 'content'},
    },
    'write_readme': {
        'type': 'compute',
        'compute_unit': 'viz:write_readme',
        'input_map': {'content': 'readme_content', 'output_path': 'event.payload.path'},
        'output_map': {'export_path': 'path'},
    },
}

TRANSITIONS = [
    {
        'id': 't_load',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'init_defaults'],
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
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_reload_from_viewing',
        'from': 'viewing',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'clear_selection'],
    },
    {
        'id': 't_start_view',
        'from': 'loaded',
        'to': 'viewing',
        'on_event': 'VIEW',
        'gates': [],
        'actions': ['render_graph'],
    },
    {
        'id': 't_switch_to_graph',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'VIEW_GRAPH',
        'gates': [],
        'actions': ['set_view_graph', 'render_graph'],
    },
    {
        'id': 't_switch_to_table',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'VIEW_TABLE',
        'gates': [],
        'actions': ['set_view_table', 'render_table'],
    },
    {
        'id': 't_switch_to_mermaid',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'VIEW_MERMAID',
        'gates': [],
        'actions': ['set_view_mermaid', 'render_mermaid'],
    },
    {
        'id': 't_select',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'SELECT',
        'gates': [],
        'actions': ['select_node'],
    },
    {
        'id': 't_deselect',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'DESELECT',
        'gates': [],
        'actions': ['clear_selection'],
    },
    {
        'id': 't_zoom_in',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'ZOOM_IN',
        'gates': [],
        'actions': ['zoom_in'],
    },
    {
        'id': 't_zoom_out',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'ZOOM_OUT',
        'gates': [],
        'actions': ['zoom_out'],
    },
    {
        'id': 't_toggle_gates',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'TOGGLE_GATES',
        'gates': [],
        'actions': ['toggle_gates'],
    },
    {
        'id': 't_toggle_actions',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'TOGGLE_ACTIONS',
        'gates': [],
        'actions': ['toggle_actions'],
    },
    {
        'id': 't_back_to_loaded',
        'from': 'viewing',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_selection'],
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
        'id': 't_unload_from_viewing',
        'from': 'viewing',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint', 'clear_selection'],
    },
    {
        'id': 't_export_readme_from_loaded',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'EXPORT_README',
        'gates': [],
        'actions': ['generate_readme', 'write_readme'],
    },
    {
        'id': 't_export_readme_from_viewing',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'EXPORT_README',
        'gates': [],
        'actions': ['generate_readme', 'write_readme'],
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
        'id': 't_load_tree',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD_TREE',
        'gates': [],
        'actions': ['load_tree', 'init_defaults'],
    },
    {
        'id': 't_set_tree',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'SET_TREE',
        'gates': [],
        'actions': ['set_tree'],
    },
    {
        'id': 't_view_tree',
        'from': 'loaded',
        'to': 'viewing',
        'on_event': 'VIEW_TREE',
        'gates': ['has_tree'],
        'actions': ['set_view_tree', 'render_tree'],
    },
    {
        'id': 't_switch_to_tree',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'VIEW_TREE',
        'gates': ['has_tree'],
        'actions': ['set_view_tree', 'render_tree'],
    },
    {
        'id': 't_switch_to_tree_mermaid',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'VIEW_TREE_MERMAID',
        'gates': ['has_tree'],
        'actions': ['set_view_tree_mermaid', 'render_tree_mermaid'],
    },
    {
        'id': 't_unload_tree',
        'from': 'viewing',
        'to': 'loaded',
        'on_event': 'UNLOAD_TREE',
        'gates': [],
        'actions': ['unload_tree'],
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
    Compiled L++ Operator: L++ Blueprint Visualizer
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_name': None, 'blueprint_id': None, 'view_mode': None, 'selected_node': None, 'zoom_level': None, 'show_gates': None, 'show_actions': None, 'output': None, 'readme_content': None, 'export_path': None, 'tree': None, 'tree_name': None, 'tree_output': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_name': None, 'blueprint_id': None, 'view_mode': None, 'selected_node': None, 'zoom_level': None, 'show_gates': None, 'show_actions': None, 'output': None, 'readme_content': None, 'export_path': None, 'tree': None, 'tree_name': None, 'tree_output': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Blueprint Visualizer')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
