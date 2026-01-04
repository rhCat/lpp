"""
L++ Compiled Operator: L++ Blueprint Registry
Version: 1.0.0
Description: Centralized blueprint management with version control, dependency tracking, and discovery

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

BLUEPRINT_ID = 'lpp_blueprint_registry'
BLUEPRINT_NAME = 'L++ Blueprint Registry'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No registry loaded, waiting for initialization
    'ready': 'ready',  # Registry loaded and ready for operations
    'viewing': 'viewing',  # Viewing a specific blueprint
    'searching': 'searching',  # Displaying search results
    'comparing': 'comparing',  # Comparing two versions
    'error': 'error',  # Error state
}

GATES = {
    'has_registry': 'index is not None',
    'no_registry': 'index is None',
    'has_blueprints': 'blueprints is not None and len(blueprints) > 0',
    'has_current': 'current_blueprint is not None',
    'has_versions': 'version_history is not None and len(version_history) > 0',
    'has_search_results': 'search_results is not None and len(search_results) > 0',
    'has_diff': 'diff_result is not None',
    'has_dependencies': 'dependency_graph is not None',
    'is_deprecated': "current_blueprint is not None and current_blueprint.get('deprecated', False) == True",
    'not_deprecated': "current_blueprint is not None and current_blueprint.get('deprecated', False) == False",
    'has_error': 'error is not None',
}

DISPLAY_RULES = [
    {'gate': 'has_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No registry loaded. Use INIT or LOAD to start.'},
    {'gate': 'is_viewing', 'template': 'Viewing: {current_id} v{current_version}'},
    {'gate': 'is_searching',
        'template': "Search: '{search_query}' - {search_results.length} results"},
    {'gate': 'is_comparing', 'template': 'Comparing versions of {current_id}'},
    {'gate': 'is_ready',
        'template': 'Registry: {stats.total} blueprints | {stats.active} active'},
    {'template': 'L++ Blueprint Registry'},
]

ACTIONS = {
    'init_registry': {
        'type': 'compute',
        'compute_unit': 'bpreg:init_registry',
        'input_map': {'registry_path': 'event.payload.path'},
        'output_map': {'registry_path': 'path', 'index': 'index', 'blueprints': 'blueprints', 'message': 'message', 'error': 'error'},
    },
    'load_registry': {
        'type': 'compute',
        'compute_unit': 'bpreg:load_registry',
        'input_map': {'registry_path': 'event.payload.path'},
        'output_map': {'registry_path': 'path', 'index': 'index', 'blueprints': 'blueprints', 'stats': 'stats', 'error': 'error'},
    },
    'save_registry': {
        'type': 'compute',
        'compute_unit': 'bpreg:save_registry',
        'input_map': {'registry_path': 'registry_path', 'index': 'index'},
        'output_map': {'message': 'message', 'error': 'error'},
    },
    'register_blueprint': {
        'type': 'compute',
        'compute_unit': 'bpreg:register_blueprint',
        'input_map': {'registry_path': 'registry_path', 'index': 'index', 'blueprint_path': 'event.payload.blueprint_path', 'tags': 'event.payload.tags', 'owner': 'event.payload.owner'},
        'output_map': {'index': 'index', 'blueprints': 'blueprints', 'message': 'message', 'error': 'error'},
    },
    'update_blueprint': {
        'type': 'compute',
        'compute_unit': 'bpreg:update_blueprint',
        'input_map': {'registry_path': 'registry_path', 'index': 'index', 'blueprint_id': 'event.payload.blueprint_id', 'blueprint_path': 'event.payload.blueprint_path', 'bump': 'event.payload.bump'},
        'output_map': {'index': 'index', 'blueprints': 'blueprints', 'current_blueprint': 'updated', 'message': 'message', 'error': 'error'},
    },
    'get_blueprint': {
        'type': 'compute',
        'compute_unit': 'bpreg:get_blueprint',
        'input_map': {'registry_path': 'registry_path', 'index': 'index', 'blueprint_id': 'event.payload.blueprint_id', 'version': 'event.payload.version'},
        'output_map': {'current_blueprint': 'blueprint', 'current_id': 'blueprint_id', 'current_version': 'version', 'error': 'error'},
    },
    'list_blueprints': {
        'type': 'compute',
        'compute_unit': 'bpreg:list_blueprints',
        'input_map': {'index': 'index', 'filter_tag': 'event.payload.tag', 'filter_deprecated': 'event.payload.show_deprecated'},
        'output_map': {'search_results': 'results', 'stats': 'stats'},
    },
    'search_blueprints': {
        'type': 'compute',
        'compute_unit': 'bpreg:search_blueprints',
        'input_map': {'index': 'index', 'query': 'event.payload.query', 'search_tags': 'event.payload.search_tags', 'search_description': 'event.payload.search_description'},
        'output_map': {'search_results': 'results', 'search_query': 'query'},
    },
    'get_versions': {
        'type': 'compute',
        'compute_unit': 'bpreg:get_versions',
        'input_map': {'index': 'index', 'blueprint_id': 'event.payload.blueprint_id'},
        'output_map': {'version_history': 'versions', 'current_id': 'blueprint_id', 'error': 'error'},
    },
    'compare_versions': {
        'type': 'compute',
        'compute_unit': 'bpreg:compare_versions',
        'input_map': {'registry_path': 'registry_path', 'blueprint_id': 'event.payload.blueprint_id', 'version_a': 'event.payload.version_a', 'version_b': 'event.payload.version_b'},
        'output_map': {'diff_result': 'diff', 'error': 'error'},
    },
    'rollback_version': {
        'type': 'compute',
        'compute_unit': 'bpreg:rollback_version',
        'input_map': {'registry_path': 'registry_path', 'index': 'index', 'blueprint_id': 'event.payload.blueprint_id', 'target_version': 'event.payload.version'},
        'output_map': {'index': 'index', 'blueprints': 'blueprints', 'current_blueprint': 'blueprint', 'message': 'message', 'error': 'error'},
    },
    'get_dependencies': {
        'type': 'compute',
        'compute_unit': 'bpreg:get_dependencies',
        'input_map': {'registry_path': 'registry_path', 'index': 'index', 'blueprint_id': 'event.payload.blueprint_id'},
        'output_map': {'dependency_graph': 'graph', 'error': 'error'},
    },
    'check_circular_deps': {
        'type': 'compute',
        'compute_unit': 'bpreg:check_circular_deps',
        'input_map': {'index': 'index', 'blueprint_id': 'event.payload.blueprint_id'},
        'output_map': {'validation_result': 'result', 'error': 'error'},
    },
    'deprecate_blueprint': {
        'type': 'compute',
        'compute_unit': 'bpreg:deprecate_blueprint',
        'input_map': {'index': 'index', 'blueprint_id': 'event.payload.blueprint_id', 'reason': 'event.payload.reason'},
        'output_map': {'index': 'index', 'blueprints': 'blueprints', 'message': 'message', 'error': 'error'},
    },
    'delete_blueprint': {
        'type': 'compute',
        'compute_unit': 'bpreg:delete_blueprint',
        'input_map': {'registry_path': 'registry_path', 'index': 'index', 'blueprint_id': 'event.payload.blueprint_id', 'delete_files': 'event.payload.delete_files'},
        'output_map': {'index': 'index', 'blueprints': 'blueprints', 'message': 'message', 'error': 'error'},
    },
    'export_registry': {
        'type': 'compute',
        'compute_unit': 'bpreg:export_registry',
        'input_map': {'index': 'index', 'format': 'event.payload.format'},
        'output_map': {'export_data': 'data', 'error': 'error'},
    },
    'get_stats': {
        'type': 'compute',
        'compute_unit': 'bpreg:get_stats',
        'input_map': {'index': 'index'},
        'output_map': {'stats': 'stats'},
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
    'clear_current': {
        'type': 'set',
        'target': 'current_blueprint',
    },
    'clear_search': {
        'type': 'set',
        'target': 'search_results',
    },
    'clear_diff': {
        'type': 'set',
        'target': 'diff_result',
    },
}

TRANSITIONS = [
    {
        'id': 't_init_registry',
        'from': 'idle',
        'to': 'ready',
        'on_event': 'INIT',
        'gates': [],
        'actions': ['init_registry', 'save_registry'],
    },
    {
        'id': 't_load_registry',
        'from': 'idle',
        'to': 'ready',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_registry'],
    },
    {
        'id': 't_reload_registry',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_registry'],
    },
    {
        'id': 't_register',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'REGISTER',
        'gates': ['has_registry'],
        'actions': ['register_blueprint', 'save_registry'],
    },
    {
        'id': 't_update',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'UPDATE',
        'gates': ['has_registry'],
        'actions': ['update_blueprint', 'save_registry'],
    },
    {
        'id': 't_update_from_viewing',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'UPDATE',
        'gates': ['has_current'],
        'actions': ['update_blueprint', 'save_registry'],
    },
    {
        'id': 't_get',
        'from': 'ready',
        'to': 'viewing',
        'on_event': 'GET',
        'gates': ['has_registry'],
        'actions': ['get_blueprint'],
    },
    {
        'id': 't_get_another',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'GET',
        'gates': [],
        'actions': ['get_blueprint'],
    },
    {
        'id': 't_list',
        'from': 'ready',
        'to': 'searching',
        'on_event': 'LIST',
        'gates': ['has_registry'],
        'actions': ['list_blueprints'],
    },
    {
        'id': 't_search',
        'from': 'ready',
        'to': 'searching',
        'on_event': 'SEARCH',
        'gates': ['has_registry'],
        'actions': ['search_blueprints'],
    },
    {
        'id': 't_search_again',
        'from': 'searching',
        'to': 'searching',
        'on_event': 'SEARCH',
        'gates': [],
        'actions': ['search_blueprints'],
    },
    {
        'id': 't_select_from_search',
        'from': 'searching',
        'to': 'viewing',
        'on_event': 'SELECT',
        'gates': ['has_search_results'],
        'actions': ['get_blueprint'],
    },
    {
        'id': 't_versions',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'VERSIONS',
        'gates': ['has_current'],
        'actions': ['get_versions'],
    },
    {
        'id': 't_compare',
        'from': 'viewing',
        'to': 'comparing',
        'on_event': 'COMPARE',
        'gates': ['has_versions'],
        'actions': ['compare_versions'],
    },
    {
        'id': 't_compare_again',
        'from': 'comparing',
        'to': 'comparing',
        'on_event': 'COMPARE',
        'gates': [],
        'actions': ['compare_versions'],
    },
    {
        'id': 't_rollback',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'ROLLBACK',
        'gates': ['has_versions'],
        'actions': ['rollback_version', 'save_registry'],
    },
    {
        'id': 't_deps',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'DEPS',
        'gates': ['has_current'],
        'actions': ['get_dependencies'],
    },
    {
        'id': 't_check_deps',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'CHECK_DEPS',
        'gates': ['has_current'],
        'actions': ['check_circular_deps'],
    },
    {
        'id': 't_deprecate',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'DEPRECATE',
        'gates': ['has_current', 'not_deprecated'],
        'actions': ['deprecate_blueprint', 'save_registry'],
    },
    {
        'id': 't_delete',
        'from': 'viewing',
        'to': 'ready',
        'on_event': 'DELETE',
        'gates': ['has_current'],
        'actions': ['delete_blueprint', 'save_registry', 'clear_current'],
    },
    {
        'id': 't_delete_from_ready',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'DELETE',
        'gates': ['has_registry'],
        'actions': ['delete_blueprint', 'save_registry'],
    },
    {
        'id': 't_export',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'EXPORT',
        'gates': ['has_registry'],
        'actions': ['export_registry'],
    },
    {
        'id': 't_export_from_viewing',
        'from': 'viewing',
        'to': 'viewing',
        'on_event': 'EXPORT',
        'gates': [],
        'actions': ['export_registry'],
    },
    {
        'id': 't_stats',
        'from': 'ready',
        'to': 'ready',
        'on_event': 'STATS',
        'gates': ['has_registry'],
        'actions': ['get_stats'],
    },
    {
        'id': 't_back_from_viewing',
        'from': 'viewing',
        'to': 'ready',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_current'],
    },
    {
        'id': 't_back_from_searching',
        'from': 'searching',
        'to': 'ready',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_search'],
    },
    {
        'id': 't_back_from_comparing',
        'from': 'comparing',
        'to': 'viewing',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_diff'],
    },
    {
        'id': 't_error_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_error'],
    },
    {
        'id': 't_load_failed',
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
    Compiled L++ Operator: L++ Blueprint Registry
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'registry_path': None, 'index': None, 'blueprints': None, 'current_blueprint': None, 'current_id': None, 'current_version': None, 'version_history': None,
                        'dependency_graph': None, 'search_results': None, 'search_query': None, 'diff_result': None, 'validation_result': None, 'export_data': None, 'stats': None, 'error': None, 'message': None}
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
        self.context = {'_state': ENTRY_STATE, 'registry_path': None, 'index': None, 'blueprints': None, 'current_blueprint': None, 'current_id': None, 'current_version': None, 'version_history': None,
                        'dependency_graph': None, 'search_results': None, 'search_query': None, 'diff_result': None, 'validation_result': None, 'export_data': None, 'stats': None, 'error': None, 'message': None}
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
    print('L++ Compiled Operator: L++ Blueprint Registry')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
