"""
L++ Compiled Operator: Hierarchical Task Orchestrator
Version: 2.0.0
Description: Hierarchical feature analysis with atomic compute units.

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

BLUEPRINT_ID = 'task_orchestrator'
BLUEPRINT_NAME = 'Hierarchical Task Orchestrator'
BLUEPRINT_VERSION = '2.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = {'complete'}

STATES = {
    'idle': 'idle',  # Awaiting task
    'analyzing': 'analyzing',  # Root analysis
    'expanding': 'expanding',  # Expand sub-features
    'planning': 'planning',  # Plan leaf execution
    'building': 'building',  # Build tools
    'executing': 'executing',  # Execute leaf
    'traversing': 'traversing',  # Next leaf
    'reflecting': 'reflecting',  # Reflect on progress
    'evaluating': 'evaluating',  # Evaluate completion
    'complete': 'complete',  # Done
    'error': 'error',  # Error
}

GATES = {
    'has_task': "task is not None and task != ''",
    'has_tree': 'feature_tree is not None',
    'can_expand': 'depth < max_depth and is_leaf == False',
    'is_atomic': 'is_leaf == True or depth >= max_depth',
    'needs_tools': 'tools_pending is not None and tools_pending > 0',
    'no_tools': 'tools_pending is None or tools_pending == 0',
    'has_more': 'exec_count < leaf_count',
    'all_done': 'exec_count >= leaf_count',
    'is_complete': 'is_complete == True',
    'not_complete': 'is_complete is None or is_complete == False',
    'within_iter': 'iteration < max_iterations',
    'max_iter': 'iteration >= max_iterations',
    'has_error': 'error is not None',
    'no_error': 'error is None',
}

DISPLAY_RULES = [
    {'gate': 'has_error', 'template': 'ERR: {error}'},
    {'gate': 'is_complete', 'template': 'DONE: {evaluation}'},
    {'gate': 'has_task', 'template': '{task} D:{depth} I:{iteration}'},
    {'template': 'Ready'},
]

ACTIONS = {
    'init': {
        'type': 'compute',
        'compute_unit': 'orch:init',
        'output_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'max_depth': 'max_depth', 'max_iterations': 'max_iterations', 'iteration': 'iteration', 'workspace_path': 'workspace_path'},
    },
    'set_task': {
        'type': 'set',
        'target': 'task',
        'value_from': 'event.payload.task',
    },
    'analyze_root': {
        'type': 'compute',
        'compute_unit': 'orch:analyze_root',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'task': 'task'},
        'output_map': {'feature_tree': 'feature_tree', 'current_path': 'current_path', 'current_feature': 'current_feature', 'depth': 'depth', 'is_leaf': 'is_leaf', 'error': 'error'},
    },
    'expand': {
        'type': 'compute',
        'compute_unit': 'orch:expand',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'feature_tree': 'feature_tree', 'current_path': 'current_path', 'current_feature': 'current_feature', 'depth': 'depth', 'max_depth': 'max_depth'},
        'output_map': {'feature_tree': 'feature_tree', 'current_feature': 'current_feature', 'depth': 'depth', 'is_leaf': 'is_leaf', 'error': 'error'},
    },
    'collect': {
        'type': 'compute',
        'compute_unit': 'orch:collect',
        'input_map': {'feature_tree': 'feature_tree'},
        'output_map': {'leaf_queue': 'leaf_queue', 'leaf_count': 'leaf_count', 'exec_count': 'exec_count', 'error': 'error'},
    },
    'plan_leaf': {
        'type': 'compute',
        'compute_unit': 'orch:plan_leaf',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'leaf_queue': 'leaf_queue', 'exec_count': 'exec_count', 'workspace_path': 'workspace_path'},
        'output_map': {'current_feature': 'current_feature', 'tools_needed': 'tools_needed', 'tools_pending': 'tools_pending', 'error': 'error'},
    },
    'build': {
        'type': 'compute',
        'compute_unit': 'orch:build',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'tools_needed': 'tools_needed', 'tools_pending': 'tools_pending', 'tools_built': 'tools_built', 'workspace_path': 'workspace_path'},
        'output_map': {'tools_needed': 'tools_needed', 'tools_pending': 'tools_pending', 'tools_built': 'tools_built', 'error': 'error'},
    },
    'exec_leaf': {
        'type': 'compute',
        'compute_unit': 'orch:exec_leaf',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'current_feature': 'current_feature', 'leaf_queue': 'leaf_queue', 'exec_count': 'exec_count', 'exec_log': 'exec_log', 'workspace_path': 'workspace_path'},
        'output_map': {'leaf_queue': 'leaf_queue', 'exec_count': 'exec_count', 'exec_log': 'exec_log', 'error': 'error'},
    },
    'next_leaf': {
        'type': 'compute',
        'compute_unit': 'orch:next_leaf',
        'input_map': {'leaf_queue': 'leaf_queue', 'exec_count': 'exec_count', 'leaf_count': 'leaf_count'},
        'output_map': {'current_feature': 'current_feature', 'tools_pending': 'tools_pending', 'error': 'error'},
    },
    'reflect': {
        'type': 'compute',
        'compute_unit': 'orch:reflect',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'task': 'task', 'feature_tree': 'feature_tree', 'exec_log': 'exec_log', 'iteration': 'iteration'},
        'output_map': {'reflection': 'reflection', 'feature_tree': 'feature_tree', 'error': 'error'},
    },
    'evaluate': {
        'type': 'compute',
        'compute_unit': 'orch:evaluate',
        'input_map': {'api_key': 'api_key', 'api_base': 'api_base', 'model': 'model', 'task': 'task', 'feature_tree': 'feature_tree', 'exec_log': 'exec_log', 'reflection': 'reflection', 'iteration': 'iteration', 'max_iterations': 'max_iterations'},
        'output_map': {'evaluation': 'evaluation', 'is_complete': 'is_complete', 'error': 'error'},
    },
    'incr': {
        'type': 'compute',
        'compute_unit': 'orch:incr',
        'input_map': {'iteration': 'iteration'},
        'output_map': {'iteration': 'iteration'},
    },
    'reset_exec': {
        'type': 'compute',
        'compute_unit': 'orch:reset_exec',
        'output_map': {'exec_count': 'exec_count', 'tools_pending': 'tools_pending'},
    },
    'clear_err': {
        'type': 'set',
        'target': 'error',
    },
}

TRANSITIONS = [
    {
        'id': 't_start',
        'from': 'idle',
        'to': 'idle',
        'on_event': 'START',
        'gates': [],
        'actions': ['init'],
    },
    {
        'id': 't_submit',
        'from': 'idle',
        'to': 'analyzing',
        'on_event': 'SUBMIT',
        'gates': [],
        'actions': ['set_task', 'analyze_root'],
    },
    {
        'id': 't_ana_expand',
        'from': 'analyzing',
        'to': 'expanding',
        'on_event': 'DONE',
        'gates': ['has_tree', 'can_expand', 'no_error'],
        'actions': ['expand'],
    },
    {
        'id': 't_ana_atomic',
        'from': 'analyzing',
        'to': 'planning',
        'on_event': 'DONE',
        'gates': ['has_tree', 'is_atomic', 'no_error'],
        'actions': ['collect', 'plan_leaf'],
    },
    {
        'id': 't_ana_err',
        'from': 'analyzing',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_exp_more',
        'from': 'expanding',
        'to': 'expanding',
        'on_event': 'DONE',
        'gates': ['can_expand', 'no_error'],
        'actions': ['expand'],
    },
    {
        'id': 't_exp_done',
        'from': 'expanding',
        'to': 'planning',
        'on_event': 'DONE',
        'gates': ['is_atomic', 'no_error'],
        'actions': ['collect', 'plan_leaf'],
    },
    {
        'id': 't_exp_err',
        'from': 'expanding',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_plan_build',
        'from': 'planning',
        'to': 'building',
        'on_event': 'DONE',
        'gates': ['needs_tools', 'no_error'],
        'actions': ['build'],
    },
    {
        'id': 't_plan_exec',
        'from': 'planning',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['no_tools', 'no_error'],
        'actions': ['exec_leaf'],
    },
    {
        'id': 't_plan_err',
        'from': 'planning',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_bld_more',
        'from': 'building',
        'to': 'building',
        'on_event': 'DONE',
        'gates': ['needs_tools', 'no_error'],
        'actions': ['build'],
    },
    {
        'id': 't_bld_done',
        'from': 'building',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['no_tools', 'no_error'],
        'actions': ['exec_leaf'],
    },
    {
        'id': 't_bld_err',
        'from': 'building',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_exec_next',
        'from': 'executing',
        'to': 'traversing',
        'on_event': 'DONE',
        'gates': ['has_more', 'no_error'],
        'actions': ['next_leaf'],
    },
    {
        'id': 't_exec_done',
        'from': 'executing',
        'to': 'reflecting',
        'on_event': 'DONE',
        'gates': ['all_done', 'no_error'],
        'actions': ['reflect'],
    },
    {
        'id': 't_exec_err',
        'from': 'executing',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_trav_build',
        'from': 'traversing',
        'to': 'building',
        'on_event': 'DONE',
        'gates': ['needs_tools', 'no_error'],
        'actions': ['build'],
    },
    {
        'id': 't_trav_exec',
        'from': 'traversing',
        'to': 'executing',
        'on_event': 'DONE',
        'gates': ['no_tools', 'no_error'],
        'actions': ['exec_leaf'],
    },
    {
        'id': 't_trav_err',
        'from': 'traversing',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_refl_ok',
        'from': 'reflecting',
        'to': 'evaluating',
        'on_event': 'DONE',
        'gates': ['no_error'],
        'actions': ['evaluate', 'incr'],
    },
    {
        'id': 't_refl_err',
        'from': 'reflecting',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_eval_complete',
        'from': 'evaluating',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['is_complete', 'no_error'],
        'actions': [],
    },
    {
        'id': 't_eval_continue',
        'from': 'evaluating',
        'to': 'expanding',
        'on_event': 'DONE',
        'gates': ['not_complete', 'within_iter', 'no_error'],
        'actions': ['reset_exec', 'expand'],
    },
    {
        'id': 't_eval_max',
        'from': 'evaluating',
        'to': 'complete',
        'on_event': 'DONE',
        'gates': ['max_iter'],
        'actions': [],
    },
    {
        'id': 't_eval_err',
        'from': 'evaluating',
        'to': 'error',
        'on_event': 'DONE',
        'gates': ['has_error'],
        'actions': [],
    },
    {
        'id': 't_recover',
        'from': 'error',
        'to': 'idle',
        'on_event': 'RETRY',
        'gates': [],
        'actions': ['clear_err'],
    },
    {
        'id': 't_reset',
        'from': '*',
        'to': 'idle',
        'on_event': 'RESET',
        'gates': [],
        'actions': [],
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
    Compiled L++ Operator: Hierarchical Task Orchestrator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'api_key': None, 'api_base': None, 'model': None, 'task': None, 'feature_tree': None, 'current_path': None, 'current_feature': None, 'depth': None, 'max_depth': None, 'is_leaf': None, 'leaf_queue': None, 'leaf_count': None,
                        'exec_count': None, 'tools_needed': None, 'tools_pending': None, 'tools_built': None, 'exec_log': None, 'reflection': None, 'evaluation': None, 'is_complete': None, 'iteration': None, 'max_iterations': None, 'workspace_path': None, 'error': None}
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
        self.context = {'_state': ENTRY_STATE, 'api_key': None, 'api_base': None, 'model': None, 'task': None, 'feature_tree': None, 'current_path': None, 'current_feature': None, 'depth': None, 'max_depth': None, 'is_leaf': None, 'leaf_queue': None, 'leaf_count': None,
                        'exec_count': None, 'tools_needed': None, 'tools_pending': None, 'tools_built': None, 'exec_log': None, 'reflection': None, 'evaluation': None, 'is_complete': None, 'iteration': None, 'max_iterations': None, 'workspace_path': None, 'error': None}
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
    print('L++ Compiled Operator: Hierarchical Task Orchestrator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
