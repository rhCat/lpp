"""
L++ Compiled Operator: L++ Event Sequence Simulator
Version: 1.0.0
Description: Interactive simulation of L++ blueprints for what-if analysis and state space exploration

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

BLUEPRINT_ID = 'lpp_event_simulator'
BLUEPRINT_NAME = 'L++ Event Sequence Simulator'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'ready': 'ready',  # Blueprint loaded, ready to simulate
    'simulating': 'simulating',  # Actively simulating, can dispatch events
    'sequence_running': 'sequence_running',  # Executing a pre-defined sequence
    'fuzzing': 'fuzzing',  # Running random event fuzzing
    'exploring': 'exploring',  # Exploring state space
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_trace': 'trace is not None and len(trace) > 0',
    'can_step_back': 'trace is not None and len(trace) > 1',
    'has_forks': 'forks is not None and len(forks) > 0',
    'has_sequence': 'sequence is not None and len(sequence) > 0',
    'sequence_not_done': 'sequence is not None and sequence_index < len(sequence)',
    'sequence_done': 'sequence is None or sequence_index >= len(sequence)',
    'has_state_space': 'state_space is not None',
    'has_path_result': 'path_result is not None',
    'is_idle': "_state == 'idle'",
    'is_ready': "_state == 'ready'",
    'is_simulating': "_state == 'simulating'",
    'is_error': "_state == 'error'",
}

DISPLAY_RULES = [
    {'gate': 'is_error', 'template': 'ERROR: {error}'},
    {'gate': 'is_idle', 'template': 'No blueprint loaded. Use LOAD command.'},
    {'gate': 'is_simulating',
        'template': '[{mode}] {blueprint_name} @ {sim_state}'},
    {'gate': 'is_ready', 'template': 'Loaded: {blueprint_name} - Ready to simulate'},
    {'template': 'L++ Event Simulator'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'sim:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'blueprint_path', 'blueprint_name': 'blueprint_name', 'blueprint_id': 'blueprint_id', 'error': 'error'},
    },
    'init_simulation': {
        'type': 'compute',
        'compute_unit': 'sim:init_simulation',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'trace': 'trace', 'forks': 'forks', 'current_fork': 'current_fork', 'mode': 'mode'},
    },
    'set_context': {
        'type': 'compute',
        'compute_unit': 'sim:set_context',
        'input_map': {'sim_context': 'sim_context', 'key': 'event.payload.key', 'value': 'event.payload.value'},
        'output_map': {'sim_context': 'sim_context'},
    },
    'dispatch_event': {
        'type': 'compute',
        'compute_unit': 'sim:dispatch_event',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'event_name': 'event.payload.event_name', 'event_payload': 'event.payload.payload'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'output': 'output', 'error': 'error'},
    },
    'get_available_events': {
        'type': 'compute',
        'compute_unit': 'sim:get_available_events',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context'},
        'output_map': {'available_events': 'available_events', 'available_transitions': 'available_transitions'},
    },
    'evaluate_gates': {
        'type': 'compute',
        'compute_unit': 'sim:evaluate_gates',
        'input_map': {'blueprint': 'blueprint', 'sim_context': 'sim_context'},
        'output_map': {'output': 'output'},
    },
    'fork_simulation': {
        'type': 'compute',
        'compute_unit': 'sim:fork_simulation',
        'input_map': {'forks': 'forks', 'fork_name': 'event.payload.fork_name', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace'},
        'output_map': {'forks': 'forks', 'current_fork': 'current_fork', 'output': 'output'},
    },
    'switch_fork': {
        'type': 'compute',
        'compute_unit': 'sim:switch_fork',
        'input_map': {'forks': 'forks', 'fork_name': 'event.payload.fork_name'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'current_fork': 'current_fork', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'output': 'output', 'error': 'error'},
    },
    'step_back': {
        'type': 'compute',
        'compute_unit': 'sim:step_back',
        'input_map': {'trace': 'trace', 'blueprint': 'blueprint'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'output': 'output'},
    },
    'run_sequence': {
        'type': 'compute',
        'compute_unit': 'sim:run_sequence',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'sequence': 'sequence'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'sequence_index': 'sequence_index', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'output': 'output', 'error': 'error'},
    },
    'set_sequence': {
        'type': 'compute',
        'compute_unit': 'sim:set_sequence',
        'input_map': {'events': 'event.payload.events'},
        'output_map': {'sequence': 'sequence', 'sequence_index': 'sequence_index', 'mode': 'mode'},
    },
    'fuzz_run': {
        'type': 'compute',
        'compute_unit': 'sim:fuzz_run',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'steps': 'event.payload.steps', 'seed': 'event.payload.seed'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'fuzz_result': 'fuzz_result', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'output': 'output'},
    },
    'find_path': {
        'type': 'compute',
        'compute_unit': 'sim:find_path',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'target_state': 'event.payload.target_state'},
        'output_map': {'path_result': 'path_result', 'output': 'output'},
    },
    'explore_state_space': {
        'type': 'compute',
        'compute_unit': 'sim:explore_state_space',
        'input_map': {'blueprint': 'blueprint', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'max_depth': 'event.payload.max_depth'},
        'output_map': {'state_space': 'state_space', 'output': 'output'},
    },
    'export_trace': {
        'type': 'compute',
        'compute_unit': 'sim:export_trace',
        'input_map': {'trace': 'trace', 'blueprint_id': 'blueprint_id', 'path': 'event.payload.path'},
        'output_map': {'output': 'output'},
    },
    'import_trace': {
        'type': 'compute',
        'compute_unit': 'sim:import_trace',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'trace': 'trace', 'sequence': 'sequence', 'mode': 'mode', 'output': 'output', 'error': 'error'},
    },
    'reset_simulation': {
        'type': 'compute',
        'compute_unit': 'sim:reset_simulation',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'sim_state': 'sim_state', 'sim_context': 'sim_context', 'trace': 'trace', 'available_events': 'available_events', 'available_transitions': 'available_transitions', 'mode': 'mode', 'output': 'output'},
    },
    'render_status': {
        'type': 'compute',
        'compute_unit': 'sim:render_status',
        'input_map': {'blueprint_name': 'blueprint_name', 'sim_state': 'sim_state', 'sim_context': 'sim_context', 'available_events': 'available_events', 'trace': 'trace', 'mode': 'mode', 'current_fork': 'current_fork'},
        'output_map': {'output': 'output'},
    },
    'render_trace': {
        'type': 'compute',
        'compute_unit': 'sim:render_trace',
        'input_map': {'trace': 'trace'},
        'output_map': {'output': 'output'},
    },
    'render_state_space': {
        'type': 'compute',
        'compute_unit': 'sim:render_state_space',
        'input_map': {'state_space': 'state_space'},
        'output_map': {'output': 'output'},
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
    'set_mode_manual': {
        'type': 'set',
        'target': 'mode',
        'value': 'manual',
    },
    'set_mode_sequence': {
        'type': 'set',
        'target': 'mode',
        'value': 'sequence',
    },
    'set_mode_fuzzing': {
        'type': 'set',
        'target': 'mode',
        'value': 'fuzzing',
    },
    'set_mode_replay': {
        'type': 'set',
        'target': 'mode',
        'value': 'replay',
    },
    'unload_blueprint': {
        'type': 'set',
        'target': 'blueprint',
    },
}

TRANSITIONS = [
    {
        'id': 't_load',
        'from': 'idle',
        'to': 'ready',
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
        'from': 'ready',
        'to': 'ready',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_reload_from_sim',
        'from': 'simulating',
        'to': 'ready',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint'],
    },
    {
        'id': 't_start_simulation',
        'from': 'ready',
        'to': 'simulating',
        'on_event': 'START',
        'gates': ['has_blueprint'],
        'actions': ['init_simulation', 'render_status'],
    },
    {
        'id': 't_dispatch',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'DISPATCH',
        'gates': [],
        'actions': ['dispatch_event'],
    },
    {
        'id': 't_set_context',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'SET_CONTEXT',
        'gates': [],
        'actions': ['set_context', 'get_available_events'],
    },
    {
        'id': 't_refresh_events',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'REFRESH',
        'gates': [],
        'actions': ['get_available_events', 'render_status'],
    },
    {
        'id': 't_evaluate_gates',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'EVAL_GATES',
        'gates': [],
        'actions': ['evaluate_gates'],
    },
    {
        'id': 't_fork',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'FORK',
        'gates': [],
        'actions': ['fork_simulation'],
    },
    {
        'id': 't_switch_fork',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'SWITCH_FORK',
        'gates': ['has_forks'],
        'actions': ['switch_fork'],
    },
    {
        'id': 't_step_back',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'STEP_BACK',
        'gates': ['can_step_back'],
        'actions': ['step_back'],
    },
    {
        'id': 't_set_sequence',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'SET_SEQUENCE',
        'gates': [],
        'actions': ['set_sequence'],
    },
    {
        'id': 't_run_sequence',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'RUN_SEQUENCE',
        'gates': ['has_sequence'],
        'actions': ['run_sequence'],
    },
    {
        'id': 't_fuzz',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'FUZZ',
        'gates': [],
        'actions': ['fuzz_run'],
    },
    {
        'id': 't_find_path',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'FIND_PATH',
        'gates': [],
        'actions': ['find_path'],
    },
    {
        'id': 't_explore',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'EXPLORE',
        'gates': [],
        'actions': ['explore_state_space'],
    },
    {
        'id': 't_view_trace',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'VIEW_TRACE',
        'gates': [],
        'actions': ['render_trace'],
    },
    {
        'id': 't_view_space',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'VIEW_SPACE',
        'gates': ['has_state_space'],
        'actions': ['render_state_space'],
    },
    {
        'id': 't_export',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'EXPORT',
        'gates': ['has_trace'],
        'actions': ['export_trace'],
    },
    {
        'id': 't_import',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'IMPORT',
        'gates': [],
        'actions': ['import_trace'],
    },
    {
        'id': 't_reset',
        'from': 'simulating',
        'to': 'simulating',
        'on_event': 'RESET',
        'gates': [],
        'actions': ['reset_simulation'],
    },
    {
        'id': 't_back_to_ready',
        'from': 'simulating',
        'to': 'ready',
        'on_event': 'STOP',
        'gates': [],
        'actions': [],
    },
    {
        'id': 't_unload',
        'from': 'ready',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint'],
    },
    {
        'id': 't_unload_from_sim',
        'from': 'simulating',
        'to': 'idle',
        'on_event': 'UNLOAD',
        'gates': [],
        'actions': ['unload_blueprint'],
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
    Compiled L++ Operator: L++ Event Sequence Simulator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'blueprint_id': None, 'sim_state': None, 'sim_context': None, 'available_events': None, 'available_transitions': None,
                        'trace': None, 'forks': None, 'current_fork': None, 'state_space': None, 'path_result': None, 'fuzz_config': None, 'fuzz_result': None, 'sequence': None, 'sequence_index': None, 'mode': None, 'output': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'blueprint_name': None, 'blueprint_id': None, 'sim_state': None, 'sim_context': None, 'available_events': None, 'available_transitions': None,
                        'trace': None, 'forks': None, 'current_fork': None, 'state_space': None, 'path_result': None, 'fuzz_config': None, 'fuzz_result': None, 'sequence': None, 'sequence_index': None, 'mode': None, 'output': None, 'error': None}
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
    print('L++ Compiled Operator: L++ Event Sequence Simulator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
