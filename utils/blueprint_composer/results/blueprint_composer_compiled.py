"""
L++ Compiled Operator: L++ Blueprint Composer
Version: 1.0.0
Description: Hierarchical composition tool for L++ blueprints - embeds sub-blueprints as macro states

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

BLUEPRINT_ID = 'lpp_blueprint_composer'
BLUEPRINT_NAME = 'L++ Blueprint Composer'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprints loaded, waiting for input
    'parent_loaded': 'parent_loaded',  # Parent blueprint loaded, waiting for child or embedding
    'child_loaded': 'child_loaded',  # Both parent and child loaded, ready to define embedding
    'defining_embedding': 'defining_embedding',  # Defining embedding parameters (target state, contract, event map)
    'embedding_ready': 'embedding_ready',  # Embedding defined, ready to compose or add more
    'composed': 'composed',  # Composition complete, ready to validate or export
    'validated': 'validated',  # Validation complete, results available
    'error': 'error',  # Error state
}

GATES = {
    'has_parent': 'parent_blueprint is not None',
    'has_child': 'child_blueprint is not None',
    'has_both': 'parent_blueprint is not None and child_blueprint is not None',
    'has_embedding': 'current_embedding is not None',
    'has_embeddings': 'embeddings is not None and len(embeddings) > 0',
    'has_composed': 'composed_blueprint is not None',
    'has_validation': 'validation_result is not None',
    'is_valid': "validation_result is not None and len(validation_result.get('errors', [])) == 0",
    'has_errors': "validation_result is not None and len(validation_result.get('errors', [])) > 0",
    'has_manifest': 'manifest is not None',
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprints loaded. Use LOAD_PARENT to start.'},
    {'gate': 'is_parent_loaded', 'template': 'Parent: {parent_path} | Use LOAD_CHILD to add child.'},
    {'gate': 'is_child_loaded', 'template': 'Parent: {parent_path} | Child: {child_path} | Use DEFINE to start embedding.'},
    {'gate': 'is_embedding_ready', 'template': 'Embedding defined. Use COMPOSE or ADD_MORE.'},
    {'gate': 'is_composed', 'template': 'Composition complete. Use VALIDATE or EXPORT.'},
    {'gate': 'is_validated', 'template': 'Validation: {validation_result}'},
    {'template': 'L++ Blueprint Composer'},
]

ACTIONS = {
    'load_parent': {
        'type': 'compute',
        'compute_unit': 'compose:load_parent',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'parent_blueprint': 'blueprint', 'parent_path': 'path', 'error': 'error'},
    },
    'load_child': {
        'type': 'compute',
        'compute_unit': 'compose:load_child',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'child_blueprint': 'blueprint', 'child_path': 'path', 'error': 'error'},
    },
    'init_embedding': {
        'type': 'compute',
        'compute_unit': 'compose:init_embedding',
        'input_map': {'target_state': 'event.payload.target_state', 'namespace_prefix': 'event.payload.namespace_prefix'},
        'output_map': {'current_embedding': 'embedding', 'namespace_prefix': 'namespace_prefix'},
    },
    'set_input_contract': {
        'type': 'compute',
        'compute_unit': 'compose:set_input_contract',
        'input_map': {'embedding': 'current_embedding', 'input_map': 'event.payload.input_map'},
        'output_map': {'current_embedding': 'embedding'},
    },
    'set_output_contract': {
        'type': 'compute',
        'compute_unit': 'compose:set_output_contract',
        'input_map': {'embedding': 'current_embedding', 'output_map': 'event.payload.output_map'},
        'output_map': {'current_embedding': 'embedding'},
    },
    'set_event_map': {
        'type': 'compute',
        'compute_unit': 'compose:set_event_map',
        'input_map': {'embedding': 'current_embedding', 'event_map': 'event.payload.event_map'},
        'output_map': {'current_embedding': 'embedding'},
    },
    'finalize_embedding': {
        'type': 'compute',
        'compute_unit': 'compose:finalize_embedding',
        'input_map': {'embedding': 'current_embedding', 'embeddings': 'embeddings', 'child_blueprint': 'child_blueprint', 'child_path': 'child_path'},
        'output_map': {'embeddings': 'embeddings', 'current_embedding': 'current_embedding'},
    },
    'compose': {
        'type': 'compute',
        'compute_unit': 'compose:compose',
        'input_map': {'parent': 'parent_blueprint', 'embeddings': 'embeddings'},
        'output_map': {'composed_blueprint': 'composed', 'error': 'error'},
    },
    'validate_composition': {
        'type': 'compute',
        'compute_unit': 'compose:validate_composition',
        'input_map': {'composed': 'composed_blueprint', 'parent': 'parent_blueprint', 'embeddings': 'embeddings'},
        'output_map': {'validation_result': 'result'},
    },
    'flatten': {
        'type': 'compute',
        'compute_unit': 'compose:flatten',
        'input_map': {'composed': 'composed_blueprint'},
        'output_map': {'composed_blueprint': 'flattened'},
    },
    'export_composed': {
        'type': 'compute',
        'compute_unit': 'compose:export_composed',
        'input_map': {'blueprint': 'composed_blueprint', 'path': 'event.payload.path'},
        'output_map': {'export_path': 'path', 'error': 'error'},
    },
    'load_manifest': {
        'type': 'compute',
        'compute_unit': 'compose:load_manifest',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'manifest': 'manifest', 'parent_blueprint': 'parent', 'parent_path': 'parent_path', 'embeddings': 'embeddings', 'error': 'error'},
    },
    'compose_from_manifest': {
        'type': 'compute',
        'compute_unit': 'compose:compose_from_manifest',
        'input_map': {'manifest': 'manifest'},
        'output_map': {'composed_blueprint': 'composed', 'error': 'error'},
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
    'clear_child': {
        'type': 'set',
        'target': 'child_blueprint',
    },
    'clear_embeddings': {
        'type': 'set',
        'target': 'embeddings',
    },
    'clear_composed': {
        'type': 'set',
        'target': 'composed_blueprint',
    },
    'clear_all': {
        'type': 'compute',
        'compute_unit': 'compose:clear_all',
        'output_map': {'parent_blueprint': 'parent_blueprint', 'child_blueprint': 'child_blueprint', 'embeddings': 'embeddings', 'current_embedding': 'current_embedding', 'composed_blueprint': 'composed_blueprint', 'validation_result': 'validation_result', 'manifest': 'manifest'},
    },
    'generate_manifest': {
        'type': 'compute',
        'compute_unit': 'compose:generate_manifest',
        'input_map': {'parent_path': 'parent_path', 'embeddings': 'embeddings'},
        'output_map': {'manifest': 'manifest'},
    },
    'export_manifest': {
        'type': 'compute',
        'compute_unit': 'compose:export_manifest',
        'input_map': {'manifest': 'manifest', 'path': 'event.payload.path'},
        'output_map': {'export_path': 'path', 'error': 'error'},
    },
}

TRANSITIONS = [
    {
        'id': 't_load_parent_from_idle',
        'from': 'idle',
        'to': 'parent_loaded',
        'on_event': 'LOAD_PARENT',
        'gates': [],
        'actions': ['load_parent'],
    },
    {
        'id': 't_load_manifest',
        'from': 'idle',
        'to': 'composed',
        'on_event': 'LOAD_MANIFEST',
        'gates': [],
        'actions': ['load_manifest', 'compose_from_manifest'],
    },
    {
        'id': 't_load_child',
        'from': 'parent_loaded',
        'to': 'child_loaded',
        'on_event': 'LOAD_CHILD',
        'gates': ['has_parent'],
        'actions': ['load_child'],
    },
    {
        'id': 't_reload_parent',
        'from': 'parent_loaded',
        'to': 'parent_loaded',
        'on_event': 'LOAD_PARENT',
        'gates': [],
        'actions': ['load_parent', 'clear_embeddings'],
    },
    {
        'id': 't_reload_child',
        'from': 'child_loaded',
        'to': 'child_loaded',
        'on_event': 'LOAD_CHILD',
        'gates': [],
        'actions': ['load_child'],
    },
    {
        'id': 't_define_embedding',
        'from': 'child_loaded',
        'to': 'defining_embedding',
        'on_event': 'DEFINE',
        'gates': ['has_both'],
        'actions': ['init_embedding'],
    },
    {
        'id': 't_set_input',
        'from': 'defining_embedding',
        'to': 'defining_embedding',
        'on_event': 'SET_INPUT',
        'gates': ['has_embedding'],
        'actions': ['set_input_contract'],
    },
    {
        'id': 't_set_output',
        'from': 'defining_embedding',
        'to': 'defining_embedding',
        'on_event': 'SET_OUTPUT',
        'gates': ['has_embedding'],
        'actions': ['set_output_contract'],
    },
    {
        'id': 't_set_events',
        'from': 'defining_embedding',
        'to': 'defining_embedding',
        'on_event': 'SET_EVENTS',
        'gates': ['has_embedding'],
        'actions': ['set_event_map'],
    },
    {
        'id': 't_done_defining',
        'from': 'defining_embedding',
        'to': 'embedding_ready',
        'on_event': 'DONE',
        'gates': ['has_embedding'],
        'actions': ['finalize_embedding'],
    },
    {
        'id': 't_add_more',
        'from': 'embedding_ready',
        'to': 'child_loaded',
        'on_event': 'ADD_MORE',
        'gates': [],
        'actions': ['clear_child'],
    },
    {
        'id': 't_compose',
        'from': 'embedding_ready',
        'to': 'composed',
        'on_event': 'COMPOSE',
        'gates': ['has_embeddings'],
        'actions': ['compose'],
    },
    {
        'id': 't_quick_compose',
        'from': 'child_loaded',
        'to': 'composed',
        'on_event': 'QUICK_COMPOSE',
        'gates': ['has_both'],
        'actions': ['init_embedding', 'finalize_embedding', 'compose'],
    },
    {
        'id': 't_validate',
        'from': 'composed',
        'to': 'validated',
        'on_event': 'VALIDATE',
        'gates': ['has_composed'],
        'actions': ['validate_composition'],
    },
    {
        'id': 't_flatten',
        'from': 'composed',
        'to': 'composed',
        'on_event': 'FLATTEN',
        'gates': ['has_composed'],
        'actions': ['flatten'],
    },
    {
        'id': 't_export',
        'from': 'composed',
        'to': 'composed',
        'on_event': 'EXPORT',
        'gates': ['has_composed'],
        'actions': ['export_composed'],
    },
    {
        'id': 't_export_after_validate',
        'from': 'validated',
        'to': 'validated',
        'on_event': 'EXPORT',
        'gates': ['has_composed'],
        'actions': ['export_composed'],
    },
    {
        'id': 't_save_manifest',
        'from': 'embedding_ready',
        'to': 'embedding_ready',
        'on_event': 'SAVE_MANIFEST',
        'gates': ['has_embeddings'],
        'actions': ['generate_manifest', 'export_manifest'],
    },
    {
        'id': 't_revalidate',
        'from': 'validated',
        'to': 'validated',
        'on_event': 'VALIDATE',
        'gates': ['has_composed'],
        'actions': ['validate_composition'],
    },
    {
        'id': 't_back_to_composed',
        'from': 'validated',
        'to': 'composed',
        'on_event': 'BACK',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_back_to_embedding',
        'from': 'composed',
        'to': 'embedding_ready',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_composed'],
    },
    {
        'id': 't_back_from_defining',
        'from': 'defining_embedding',
        'to': 'child_loaded',
        'on_event': 'CANCEL',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_reset',
        'from': 'composed',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_reset_from_validated',
        'from': 'validated',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_clear_from_parent',
        'from': 'parent_loaded',
        'to': 'idle',
        'on_event': 'CLEAR',
        'gates': [],
        'actions': ['clear_all'],
    },
    {
        'id': 't_clear_from_child',
        'from': 'child_loaded',
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
    Compiled L++ Operator: L++ Blueprint Composer
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'parent_blueprint': None, 'parent_path': None, 'child_blueprint': None, 'child_path': None, 'embeddings': None, 'current_embedding': None, 'composed_blueprint': None, 'validation_result': None, 'manifest': None, 'export_path': None, 'error': None, 'namespace_prefix': None}
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
        self.context = {'_state': ENTRY_STATE, 'parent_blueprint': None, 'parent_path': None, 'child_blueprint': None, 'child_path': None, 'embeddings': None, 'current_embedding': None, 'composed_blueprint': None, 'validation_result': None, 'manifest': None, 'export_path': None, 'error': None, 'namespace_prefix': None}
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
    print('L++ Compiled Operator: L++ Blueprint Composer')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
