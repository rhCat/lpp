"""
L++ Compiled Operator: L++ Schema Migrator
Version: 1.0.0
Description: Tool for migrating L++ blueprints between schema versions

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

BLUEPRINT_ID = 'lpp_schema_migrator'
BLUEPRINT_NAME = 'L++ Schema Migrator'
BLUEPRINT_VERSION = '1.0.0'
ENTRY_STATE = 'idle'
TERMINAL_STATES = set()

STATES = {
    'idle': 'idle',  # No blueprint loaded, waiting for input
    'loaded': 'loaded',  # Blueprint loaded, version detected
    'planning': 'planning',  # Planning migration path
    'planned': 'planned',  # Migration plan ready, awaiting execution
    'migrating': 'migrating',  # Applying migration steps
    'validating': 'validating',  # Validating migrated blueprint
    'complete': 'complete',  # Migration complete, ready to export
    'batch_mode': 'batch_mode',  # Processing batch migration
    'error': 'error',  # Error state
}

GATES = {
    'has_blueprint': 'blueprint is not None',
    'no_blueprint': 'blueprint is None',
    'has_migration_plan': 'migration_plan is not None and len(migration_plan) > 0',
    'no_migration_needed': 'source_version == target_version',
    'has_migrated_blueprint': 'migrated_blueprint is not None',
    'validation_passed': "validation_result is not None and validation_result.get('valid', False)",
    'validation_failed': "validation_result is not None and not validation_result.get('valid', True)",
    'is_dry_run': 'dry_run_mode == True',
    'has_batch_paths': 'batch_paths is not None and len(batch_paths) > 0',
}

DISPLAY_RULES = [
    {'gate': 'validation_failed',
        'template': 'VALIDATION FAILED: {validation_result.errors}'},
    {'gate': 'validation_passed', 'template': 'Migration validated successfully'},
    {'gate': 'has_migration_plan',
        'template': 'Plan: {source_version} -> {target_version} ({migration_plan} steps)'},
    {'gate': 'has_blueprint',
        'template': 'Loaded: {blueprint_path} (schema: {source_version})'},
    {'template': 'L++ Schema Migrator'},
]

ACTIONS = {
    'load_blueprint': {
        'type': 'compute',
        'compute_unit': 'migrate:load_blueprint',
        'input_map': {'path': 'event.payload.path'},
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'path', 'error': 'error'},
    },
    'detect_version': {
        'type': 'compute',
        'compute_unit': 'migrate:detect_version',
        'input_map': {'blueprint': 'blueprint'},
        'output_map': {'source_version': 'source_version', 'error': 'error'},
    },
    'set_target_version': {
        'type': 'set',
        'target': 'target_version',
        'value_from': 'event.payload.version',
    },
    'set_target_latest': {
        'type': 'compute',
        'compute_unit': 'migrate:get_latest_version',
        'output_map': {'target_version': 'version'},
    },
    'list_migrations': {
        'type': 'compute',
        'compute_unit': 'migrate:list_migrations',
        'output_map': {'available_migrations': 'migrations'},
    },
    'plan_migration': {
        'type': 'compute',
        'compute_unit': 'migrate:plan_migration',
        'input_map': {'source_version': 'source_version', 'target_version': 'target_version', 'available_migrations': 'available_migrations'},
        'output_map': {'migration_plan': 'plan', 'error': 'error'},
    },
    'analyze_changes': {
        'type': 'compute',
        'compute_unit': 'migrate:analyze_changes',
        'input_map': {'blueprint': 'blueprint', 'migration_plan': 'migration_plan'},
        'output_map': {'migration_changes': 'changes'},
    },
    'apply_migration': {
        'type': 'compute',
        'compute_unit': 'migrate:apply_migration',
        'input_map': {'blueprint': 'blueprint', 'migration_plan': 'migration_plan'},
        'output_map': {'migrated_blueprint': 'blueprint', 'error': 'error'},
    },
    'validate_blueprint': {
        'type': 'compute',
        'compute_unit': 'migrate:validate_blueprint',
        'input_map': {'blueprint': 'migrated_blueprint', 'target_version': 'target_version'},
        'output_map': {'validation_result': 'result'},
    },
    'generate_report': {
        'type': 'compute',
        'compute_unit': 'migrate:generate_report',
        'input_map': {'blueprint_path': 'blueprint_path', 'source_version': 'source_version', 'target_version': 'target_version', 'migration_plan': 'migration_plan', 'migration_changes': 'migration_changes', 'validation_result': 'validation_result', 'dry_run_mode': 'dry_run_mode'},
        'output_map': {'report': 'report'},
    },
    'export_migrated': {
        'type': 'compute',
        'compute_unit': 'migrate:export_migrated',
        'input_map': {'blueprint': 'migrated_blueprint', 'path': 'event.payload.path'},
        'output_map': {'error': 'error'},
    },
    'dry_run': {
        'type': 'compute',
        'compute_unit': 'migrate:dry_run',
        'input_map': {'blueprint': 'blueprint', 'migration_plan': 'migration_plan'},
        'output_map': {'migration_changes': 'changes', 'migrated_blueprint': 'preview_blueprint'},
    },
    'set_dry_run_on': {
        'type': 'set',
        'target': 'dry_run_mode',
        'value': True,
    },
    'set_dry_run_off': {
        'type': 'set',
        'target': 'dry_run_mode',
        'value': False,
    },
    'set_batch_paths': {
        'type': 'set',
        'target': 'batch_paths',
        'value_from': 'event.payload.paths',
    },
    'batch_migrate': {
        'type': 'compute',
        'compute_unit': 'migrate:batch_migrate',
        'input_map': {'paths': 'batch_paths', 'target_version': 'target_version'},
        'output_map': {'batch_results': 'results'},
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
    'clear_migration': {
        'type': 'compute',
        'compute_unit': 'migrate:clear_migration',
        'output_map': {'migration_plan': 'plan', 'migration_changes': 'changes', 'migrated_blueprint': 'blueprint', 'validation_result': 'validation', 'report': 'report'},
    },
    'unload_blueprint': {
        'type': 'compute',
        'compute_unit': 'migrate:unload_blueprint',
        'output_map': {'blueprint': 'blueprint', 'blueprint_path': 'path', 'source_version': 'version', 'target_version': 'target', 'migration_plan': 'plan', 'migration_changes': 'changes', 'migrated_blueprint': 'migrated', 'validation_result': 'validation', 'report': 'report'},
    },
}

TRANSITIONS = [
    {
        'id': 't_load',
        'from': 'idle',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': ['no_blueprint'],
        'actions': ['load_blueprint', 'detect_version', 'list_migrations'],
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
        'actions': ['load_blueprint', 'detect_version', 'clear_migration'],
    },
    {
        'id': 't_reload_from_complete',
        'from': 'complete',
        'to': 'loaded',
        'on_event': 'LOAD',
        'gates': [],
        'actions': ['load_blueprint', 'detect_version', 'clear_migration'],
    },
    {
        'id': 't_set_target',
        'from': 'loaded',
        'to': 'planning',
        'on_event': 'SET_TARGET',
        'gates': ['has_blueprint'],
        'actions': ['set_target_version'],
    },
    {
        'id': 't_set_target_latest',
        'from': 'loaded',
        'to': 'planning',
        'on_event': 'MIGRATE_LATEST',
        'gates': ['has_blueprint'],
        'actions': ['set_target_latest'],
    },
    {
        'id': 't_plan',
        'from': 'planning',
        'to': 'planned',
        'on_event': 'PLAN',
        'gates': [],
        'actions': ['plan_migration', 'analyze_changes'],
    },
    {
        'id': 't_auto_plan',
        'from': 'loaded',
        'to': 'planned',
        'on_event': 'PLAN_TO',
        'gates': ['has_blueprint'],
        'actions': ['set_target_version', 'plan_migration', 'analyze_changes'],
    },
    {
        'id': 't_auto_plan_latest',
        'from': 'loaded',
        'to': 'planned',
        'on_event': 'PLAN_LATEST',
        'gates': ['has_blueprint'],
        'actions': ['set_target_latest', 'plan_migration', 'analyze_changes'],
    },
    {
        'id': 't_dry_run',
        'from': 'planned',
        'to': 'complete',
        'on_event': 'DRY_RUN',
        'gates': ['has_migration_plan'],
        'actions': ['set_dry_run_on', 'dry_run', 'generate_report'],
    },
    {
        'id': 't_execute',
        'from': 'planned',
        'to': 'migrating',
        'on_event': 'EXECUTE',
        'gates': ['has_migration_plan'],
        'actions': ['set_dry_run_off', 'apply_migration'],
    },
    {
        'id': 't_validate',
        'from': 'migrating',
        'to': 'validating',
        'on_event': 'VALIDATE',
        'gates': ['has_migrated_blueprint'],
        'actions': ['validate_blueprint'],
    },
    {
        'id': 't_auto_validate',
        'from': 'migrating',
        'to': 'validating',
        'on_event': 'AUTO_CONTINUE',
        'gates': ['has_migrated_blueprint'],
        'actions': ['validate_blueprint'],
    },
    {
        'id': 't_finalize',
        'from': 'validating',
        'to': 'complete',
        'on_event': 'FINALIZE',
        'gates': ['validation_passed'],
        'actions': ['generate_report'],
    },
    {
        'id': 't_finalize_with_warnings',
        'from': 'validating',
        'to': 'complete',
        'on_event': 'FORCE_FINALIZE',
        'gates': [],
        'actions': ['generate_report'],
    },
    {
        'id': 't_migrate_all',
        'from': 'loaded',
        'to': 'complete',
        'on_event': 'MIGRATE_ALL',
        'gates': ['has_blueprint'],
        'actions': ['set_target_latest', 'plan_migration', 'analyze_changes', 'set_dry_run_off', 'apply_migration', 'validate_blueprint', 'generate_report'],
    },
    {
        'id': 't_preview_all',
        'from': 'loaded',
        'to': 'complete',
        'on_event': 'PREVIEW_ALL',
        'gates': ['has_blueprint'],
        'actions': ['set_target_latest', 'plan_migration', 'analyze_changes', 'set_dry_run_on', 'dry_run', 'generate_report'],
    },
    {
        'id': 't_export',
        'from': 'complete',
        'to': 'complete',
        'on_event': 'EXPORT',
        'gates': ['has_migrated_blueprint'],
        'actions': ['export_migrated'],
    },
    {
        'id': 't_start_batch',
        'from': 'idle',
        'to': 'batch_mode',
        'on_event': 'BATCH',
        'gates': [],
        'actions': ['set_batch_paths', 'set_target_latest'],
    },
    {
        'id': 't_batch_with_target',
        'from': 'idle',
        'to': 'batch_mode',
        'on_event': 'BATCH_TO',
        'gates': [],
        'actions': ['set_batch_paths', 'set_target_version'],
    },
    {
        'id': 't_run_batch',
        'from': 'batch_mode',
        'to': 'complete',
        'on_event': 'RUN_BATCH',
        'gates': ['has_batch_paths'],
        'actions': ['batch_migrate', 'generate_report'],
    },
    {
        'id': 't_back_to_loaded',
        'from': 'planned',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_migration'],
    },
    {
        'id': 't_back_from_complete',
        'from': 'complete',
        'to': 'loaded',
        'on_event': 'BACK',
        'gates': [],
        'actions': ['clear_migration'],
    },
    {
        'id': 't_replan',
        'from': 'planned',
        'to': 'planning',
        'on_event': 'REPLAN',
        'gates': [],
        'actions': ['clear_migration'],
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
        'actions': ['unload_blueprint'],
    },
    {
        'id': 't_unload_from_planned',
        'from': 'planned',
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
        'actions': ['clear_error', 'unload_blueprint'],
    },
    {
        'id': 't_recover_to_loaded',
        'from': 'error',
        'to': 'loaded',
        'on_event': 'RETRY',
        'gates': ['has_blueprint'],
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
    Compiled L++ Operator: L++ Schema Migrator
    """

    def __init__(self, compute_registry: dict = None):
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'source_version': None, 'target_version': None, 'available_migrations': None, 'migration_plan': None,
                        'migration_changes': None, 'migrated_blueprint': None, 'validation_result': None, 'report': None, 'error': None, 'dry_run_mode': None, 'batch_paths': None, 'batch_results': None}
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
        self.context = {'_state': ENTRY_STATE, 'blueprint': None, 'blueprint_path': None, 'source_version': None, 'target_version': None, 'available_migrations': None, 'migration_plan': None,
                        'migration_changes': None, 'migrated_blueprint': None, 'validation_result': None, 'report': None, 'error': None, 'dry_run_mode': None, 'batch_paths': None, 'batch_results': None}
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
    print('L++ Compiled Operator: L++ Schema Migrator')
    print('States:', list(STATES.keys()))
    print('Entry:', ENTRY_STATE)
    print('Transitions:', len(TRANSITIONS))
