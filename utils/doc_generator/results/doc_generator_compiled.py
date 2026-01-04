"""
L++ Compiled Operator: L++ Documentation Generator
Version: 1.0.0
Description: Auto-generates comprehensive documentation from L++ blueprints in multiple formats

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

BLUEPRINT_ID = 'lpp_doc_generator'
BLUEPRINT_NAME = 'L++ Documentation Generator'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, ready to generate docs
    'generating': 'generating',  # Actively generating documentation sections
    'assembling': 'assembling',  # Assembling all sections into final document
    'exporting': 'exporting',  # Exporting documentation to file
    'done': 'done',  # Documentation generation complete
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'format_is_markdown': "output_format == 'markdown'",
    'format_is_html': "output_format == 'html'",
    'format_is_json': "output_format == 'json'",
    'has_assembled_doc': 'assembled_doc is not None',
    'wants_mermaid': 'include_mermaid == True',
    'wants_tables': 'include_tables == True',
    'wants_quickstart': 'include_quickstart == True',
    'wants_context': 'include_context == True',
    'is_idle': "_state == 'idle'",
    'is_loaded': "_state == 'loaded'",
    'is_generating': "_state == 'generating'",
    'is_assembling': "_state == 'assembling'",
    'is_exporting': "_state == 'exporting'",
    'is_done': "_state == 'done'",
    'is_error': "_state == 'error'",
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprint loaded. Use LOAD command.'},
    {'gate': 'is_done', 'template': 'Done! Exported to: {output_path}'},
    {'gate': 'is_exporting', 'template': 'Exporting {output_format}...'},
    {'gate': 'is_assembling', 'template': 'Assembling {output_format} document...'},
    {'gate': 'is_generating', 'template': 'Generating sections for: {blueprint_name}'},
    {'gate': 'is_loaded',
        'template': 'Loaded: {blueprint_name} [{output_format}]'},
    {'template': 'L++ Documentation Generator'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'doc:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'blueprint_name': 'blueprint_name', 'blueprint_id': 'blueprint_id', 'error': 'error'},
    },
    'init_defaults': {
        'type': 'compute',
        'compute_unit': 'doc:init_defaults',
        'output_map': {'output_format': 'output_format', 'include_mermaid': 'include_mermaid', 'include_tables': 'include_tables', 'include_quickstart': 'include_quickstart', 'include_context': 'include_context'},
    },
    'set_format_markdown': {
        'type': 'set',
        'target': 'output_format',
        'value': 'markdown',
    },
    'set_format_html': {
        'type': 'set',
        'target': 'output_format',
        'value': 'html',
    },
    'set_format_json': {
        'type': 'set',
        'target': 'output_format',
        'value': 'json',
    },
    'toggle_mermaid': {
        'type': 'compute',
        'compute_unit': 'doc:toggle',
        'input_map': {'current': 'include_mermaid'},
        'output_map': {'include_mermaid': 'result'},
    },
    'toggle_tables': {
        'type': 'compute',
        'compute_unit': 'doc:toggle',
        'input_map': {'current': 'include_tables'},
        'output_map': {'include_tables': 'result'},
    },
    'toggle_quickstart': {
        'type': 'compute',
        'compute_unit': 'doc:toggle',
        'input_map': {'current': 'include_quickstart'},
        'output_map': {'include_quickstart': 'result'},
    },
    'toggle_context': {
        'type': 'compute',
        'compute_unit': 'doc:toggle',
        'input_map': {'current': 'include_context'},
        'output_map': {'include_context': 'result'},
    },
    'extract_metadata': {
        'type': 'compute',
        'compute_unit': 'doc:extract_metadata',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'metadata': 'metadata'},
    },
    'generate_overview': {
        'type': 'compute',
        'compute_unit': 'doc:generate_overview',
        'input_map': {'blueprint': 'blueprint', 'metadata': 'metadata'},
        'output_map': {'overview_section': 'section'},
    },
    'generate_mermaid': {
        'type': 'compute',
        'compute_unit': 'doc:generate_mermaid',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'mermaid_section': 'section'},
    },
    'generate_states': {
        'type': 'compute',
        'compute_unit': 'doc:generate_states_table',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'states_section': 'section'},
    },
    'generate_transitions': {
        'type': 'compute',
        'compute_unit': 'doc:generate_transitions_table',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'transitions_section': 'section'},
    },
    'generate_gates': {
        'type': 'compute',
        'compute_unit': 'doc:generate_gates_table',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'gates_section': 'section'},
    },
    'generate_actions': {
        'type': 'compute',
        'compute_unit': 'doc:generate_actions_table',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'actions_section': 'section'},
    },
    'generate_context': {
        'type': 'compute',
        'compute_unit': 'doc:generate_context_docs',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'context_section': 'section'},
    },
    'generate_events': {
        'type': 'compute',
        'compute_unit': 'doc:generate_events_list',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'events_section': 'section'},
    },
    'generate_quickstart': {
        'type': 'compute',
        'compute_unit': 'doc:generate_quickstart',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'quickstart_section': 'section'},
    },
    'assemble_markdown': {
        'type': 'compute',
        'compute_unit': 'doc:assemble_markdown',
        'input_map': {'overview_section': 'overview_section', 'mermaid_section': 'mermaid_section', 'states_section': 'states_section', 'transitions_section': 'transitions_section', 'gates_section': 'gates_section', 'actions_section': 'actions_section', 'context_section': 'context_section', 'events_section': 'events_section', 'quickstart_section': 'quickstart_section', 'include_mermaid': 'include_mermaid', 'include_tables': 'include_tables', 'include_quickstart': 'include_quickstart', 'include_context': 'include_context'},
        'output_map': {'assembled_doc': 'doc'},
    },
    'assemble_html': {
        'type': 'compute',
        'compute_unit': 'doc:assemble_html',
        'input_map': {'overview_section': 'overview_section', 'mermaid_section': 'mermaid_section', 'states_section': 'states_section', 'transitions_section': 'transitions_section', 'gates_section': 'gates_section', 'actions_section': 'actions_section', 'context_section': 'context_section', 'events_section': 'events_section', 'quickstart_section': 'quickstart_section', 'include_mermaid': 'include_mermaid', 'include_tables': 'include_tables', 'include_quickstart': 'include_quickstart', 'include_context': 'include_context', 'blueprint_name': 'blueprint_name'},
        'output_map': {'assembled_doc': 'doc'},
    },
    'assemble_json': {
        'type': 'compute',
        'compute_unit': 'doc:assemble_json',
        'input_map': {'blueprint': 'blueprint', 'metadata': 'metadata'},
        'output_map': {'assembled_doc': 'doc'},
    },
    'export_docs': {
        'type': 'compute',
        'compute_unit': 'doc:export_docs',
        'input_map': {'content': 'assembled_doc', 'path': 'event.payload.path', 'format': 'output_format'},
        'output_map': {'output_path': 'path', 'error': 'error'},
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
    'clear_sections': {
        'type': 'compute',
        'compute_unit': 'doc:clear_sections',
        'output_map': {'overview_section': 'overview_section', 'mermaid_section': 'mermaid_section', 'states_section': 'states_section', 'transitions_section': 'transitions_section', 'gates_section': 'gates_section', 'actions_section': 'actions_section', 'context_section': 'context_section', 'events_section': 'events_section', 'quickstart_section': 'quickstart_section', 'assembled_doc': 'assembled_doc'},
    },
}

TRANSITIONS = [
    {
        'id': 't_load',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': ['no_blueprint'],
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
        'actions': ['load_blueprint', 'clear_sections'],
    },
    {
        'id': 't_reload_from_done',
        'from': 'done',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'clear_sections'],
    },
    {
        'id': 't_set_markdown',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'FORMAT_MARKDOWN',
        'gates': [],
        'actions': ['set_format_markdown'],
    },
    {
        'id': 't_set_html',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'FORMAT_HTML',
        'gates': [],
        'actions': ['set_format_html'],
    },
    {
        'id': 't_set_json',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'FORMAT_JSON',
        'gates': [],
        'actions': ['set_format_json'],
    },
    {
        'id': 't_toggle_mermaid',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'TOGGLE_MERMAID',
        'gates': [],
        'actions': ['toggle_mermaid'],
    },
    {
        'id': 't_toggle_tables',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'TOGGLE_TABLES',
        'gates': [],
        'actions': ['toggle_tables'],
    },
    {
        'id': 't_toggle_quickstart',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'TOGGLE_QUICKSTART',
        'gates': [],
        'actions': ['toggle_quickstart'],
    },
    {
        'id': 't_toggle_context',
        'from': 'loaded',
        'to': 'loaded',
        'on_event': 'TOGGLE_CONTEXT',
        'gates': [],
        'actions': ['toggle_context'],
    },
    {
        'id': 't_start_generate',
        'from': 'loaded',
        'to': 'generating',
        'on_event': 'GENERATE',
        'gates': ['has_blueprint'],
        'actions': ['extract_metadata', 'generate_overview', 'generate_mermaid', 'generate_states', 'generate_transitions', 'generate_gates', 'generate_actions', 'generate_context', 'generate_events', 'generate_quickstart'],
    },
    {
        'id': 't_assemble_markdown',
        'from': 'generating',
        'to': 'assembling',
        'on_event': 'ASSEMBLE',
        'gates': ['format_is_markdown'],
        'actions': ['assemble_markdown'],
    },
    {
        'id': 't_assemble_html',
        'from': 'generating',
        'to': 'assembling',
        'on_event': 'ASSEMBLE',
        'gates': ['format_is_html'],
        'actions': ['assemble_html'],
    },
    {
        'id': 't_assemble_json',
        'from': 'generating',
        'to': 'assembling',
        'on_event': 'ASSEMBLE',
        'gates': ['format_is_json'],
        'actions': ['assemble_json'],
    },
    {
        'id': 't_export',
        'from': 'assembling',
        'to': 'exporting',
        'on_event': 'EXPORT',
        'gates': ['has_assembled_doc'],
        'actions': ['export_docs'],
    },
    {
        'id': 't_finish',
        'from': 'exporting',
        'to': 'done',
        'on_event': 'DONE',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_generate_full',
        'from': 'loaded',
        'to': 'done',
        'on_event': 'GENERATE_FULL',
        'gates': ['has_blueprint'],
        'actions': ['extract_metadata', 'generate_overview', 'generate_mermaid', 'generate_states', 'generate_transitions', 'generate_gates', 'generate_actions', 'generate_context', 'generate_events', 'generate_quickstart', 'assemble_markdown', 'export_docs'],
    },
    {
        'id': 't_back_to_loaded',
        'from': 'generating',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_back_from_assembling',
        'from': 'assembling',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_back_from_done',
        'from': 'done',
        'to': 'loaded',
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
        'actions': ['unload_blueprint', 'clear_sections'],
    },
    {
        'id': 't_unload_from_done',
        'from': 'done',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint', 'clear_sections'],
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
    Compiled L++ Operator: L++ Documentation Generator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'blueprint_id': None, 'output_format': None, 'output_path': None, 'metadata': None, 'overview_section': None, 'mermaid_section': None, 'states_section': None, 'transitions_section': None,
                        'gates_section': None, 'actions_section': None, 'context_section': None, 'events_section': None, 'quickstart_section': None, 'assembled_doc': None, 'include_mermaid': None, 'include_tables': None, 'include_quickstart': None, 'include_context': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'blueprint_id': None, 'output_format': None, 'output_path': None, 'metadata': None, 'overview_section': None, 'mermaid_section': None, 'states_section': None, 'transitions_section': None,
                        'gates_section': None, 'actions_section': None, 'context_section': None, 'events_section': None, 'quickstart_section': None, 'assembled_doc': None, 'include_mermaid': None, 'include_tables': None, 'include_quickstart': None, 'include_context': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Documentation Generator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
